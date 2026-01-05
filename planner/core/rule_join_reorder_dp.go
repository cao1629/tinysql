// Copyright 2018 PingCAP, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// See the License for the specific language governing permissions and
// limitations under the License.

package core

import (
	"github.com/pingcap/tidb/expression"
	"github.com/pingcap/tidb/parser/ast"
)

type joinReorderDPSolver struct {
	*baseSingleGroupJoinOrderSolver
	newJoin func(lChild, rChild LogicalPlan, eqConds []*expression.ScalarFunction, otherConds []expression.Expression) LogicalPlan
}

type joinGroupEqEdge struct {
	nodeIDs []int
	edge    *expression.ScalarFunction
}

type joinGroupNonEqEdge struct {
	nodeIDs    []int
	nodeIDMask uint
	expr       expression.Expression
}

func (s *joinReorderDPSolver) solve(joinGroup []LogicalPlan, eqConds []expression.Expression) (LogicalPlan, error) {
	n := len(joinGroup)
	if n == 0 {
		return nil, nil
	}
	if n == 1 {
		return joinGroup[0], nil
	}

	// Derive stats for each node
	for _, node := range joinGroup {
		_, err := node.recursiveDeriveStats()
		if err != nil {
			return nil, err
		}
	}

	// Build edge information from eqConds
	eqEdges := make([]joinGroupEqEdge, 0, len(eqConds))
	for _, cond := range eqConds {
		sf := cond.(*expression.ScalarFunction)
		lCol := sf.GetArgs()[0].(*expression.Column)
		rCol := sf.GetArgs()[1].(*expression.Column)
		lIdx, err := findNodeIndexInGroup(joinGroup, lCol)
		if err != nil {
			return nil, err
		}
		rIdx, err := findNodeIndexInGroup(joinGroup, rCol)
		if err != nil {
			return nil, err
		}
		eqEdges = append(eqEdges, joinGroupEqEdge{
			nodeIDs: []int{lIdx, rIdx},
			edge:    sf,
		})
	}

	// Build non-eq edge information from otherConds
	nonEqEdges := make([]joinGroupNonEqEdge, 0, len(s.otherConds))
	for _, cond := range s.otherConds {
		cols := expression.ExtractColumns(cond)
		mask := uint(0)
		nodeIDs := make([]int, 0)
		for _, col := range cols {
			idx, err := findNodeIndexInGroup(joinGroup, col)
			if err != nil {
				return nil, err
			}
			if mask&(1<<uint(idx)) == 0 {
				mask |= 1 << uint(idx)
				nodeIDs = append(nodeIDs, idx)
			}
		}
		nonEqEdges = append(nonEqEdges, joinGroupNonEqEdge{
			nodeIDs:    nodeIDs,
			nodeIDMask: mask,
			expr:       cond,
		})
	}

	// DP arrays
	totalMask := uint(1<<n) - 1
	bestPlan := make([]LogicalPlan, 1<<n)
	bestCost := make([]float64, 1<<n)

	// Initialize: all invalid
	for i := range bestCost {
		bestCost[i] = -1
	}

	// Initialize single nodes
	for i := 0; i < n; i++ {
		mask := uint(1 << i)
		bestPlan[mask] = joinGroup[i]
		bestCost[mask] = s.baseNodeCumCost(joinGroup[i])
	}

	// DP: enumerate all subsets
	for mask := uint(1); mask <= totalMask; mask++ {
		if bestCost[mask] >= 0 {
			// Already computed (single node)
			continue
		}

		// Try all non-empty proper subsets of mask
		// sub is a subset of mask, and mask ^ sub is the complement in mask
		for sub := mask & (mask - 1); sub > 0; sub = (sub - 1) & mask {
			comp := mask ^ sub
			if bestCost[sub] < 0 || bestCost[comp] < 0 {
				// One of the subgroups is not computed yet, skip
				continue
			}

			// Find edges connecting sub and comp
			var usedEqEdges []joinGroupEqEdge
			for _, edge := range eqEdges {
				idx1, idx2 := edge.nodeIDs[0], edge.nodeIDs[1]
				m1, m2 := uint(1<<idx1), uint(1<<idx2)
				// Check if this edge connects sub and comp
				if (sub&m1 != 0 && comp&m2 != 0) || (sub&m2 != 0 && comp&m1 != 0) {
					usedEqEdges = append(usedEqEdges, edge)
				}
			}

			// If no edge connects them, skip (handle cartesian later)
			if len(usedEqEdges) == 0 {
				continue
			}

			// Find other conditions that can be applied
			var usedOtherConds []expression.Expression
			for _, edge := range nonEqEdges {
				if edge.nodeIDMask&mask == edge.nodeIDMask {
					// All nodes of this condition are in the mask
					usedOtherConds = append(usedOtherConds, edge.expr)
				}
			}

			// Make the join - put smaller subset on left, larger on right for consistent ordering
			// When popCount is equal, use smaller mask (lower node indices) on left
			leftPlan, rightPlan := bestPlan[sub], bestPlan[comp]
			leftCost, rightCost := bestCost[sub], bestCost[comp]
			leftMask, rightMask := sub, comp
			subPC, compPC := popCount(sub), popCount(comp)
			if subPC > compPC || (subPC == compPC && sub > comp) {
				leftPlan, rightPlan = rightPlan, leftPlan
				leftCost, rightCost = rightCost, leftCost
				leftMask, rightMask = rightMask, leftMask
			}

			// Reorder edges to match the left/right assignment
			var orderedEqEdges []joinGroupEqEdge
			for _, edge := range usedEqEdges {
				idx1, idx2 := edge.nodeIDs[0], edge.nodeIDs[1]
				m1, m2 := uint(1<<idx1), uint(1<<idx2)
				// Ensure the edge goes from left to right
				if leftMask&m1 != 0 && rightMask&m2 != 0 {
					orderedEqEdges = append(orderedEqEdges, edge)
				} else if leftMask&m2 != 0 && rightMask&m1 != 0 {
					// Swap the columns in the edge
					newSf := expression.NewFunctionInternal(s.ctx, ast.EQ, edge.edge.GetType(),
						edge.edge.GetArgs()[1], edge.edge.GetArgs()[0]).(*expression.ScalarFunction)
					orderedEqEdges = append(orderedEqEdges, joinGroupEqEdge{
						nodeIDs: []int{idx2, idx1},
						edge:    newSf,
					})
				}
			}

			newJoin, err := s.newJoinWithEdge(leftPlan, rightPlan, orderedEqEdges, usedOtherConds)
			if err != nil {
				return nil, err
			}

			// Calculate cost
			leftNode := &jrNode{p: leftPlan, cumCost: leftCost}
			rightNode := &jrNode{p: rightPlan, cumCost: rightCost}
			newCost := s.calcJoinCumCost(newJoin, leftNode, rightNode)

			// Update if better
			if bestCost[mask] < 0 || newCost < bestCost[mask] {
				bestCost[mask] = newCost
				bestPlan[mask] = newJoin
			}
		}
	}

	// If the graph is connected, bestPlan[totalMask] should be set
	if bestPlan[totalMask] != nil {
		return bestPlan[totalMask], nil
	}

	// Handle disconnected graph: collect all connected components and make bushy join
	// First, identify all connected components by finding maximal valid groups
	var cartesianGroup []LogicalPlan
	remaining := totalMask

	// Process nodes in order to maintain deterministic output
	for i := 0; i < n && remaining > 0; i++ {
		nodeMask := uint(1 << i)
		if remaining&nodeMask == 0 {
			continue
		}

		// Find the largest connected component starting from this node
		var bestMask uint = nodeMask
		for mask := remaining; mask > 0; mask = (mask - 1) & remaining {
			if mask&nodeMask == 0 {
				continue
			}
			if bestPlan[mask] != nil && popCount(mask) > popCount(bestMask) {
				bestMask = mask
			}
		}

		cartesianGroup = append(cartesianGroup, bestPlan[bestMask])
		remaining &^= bestMask
	}

	return s.makeBushyJoin(cartesianGroup, s.otherConds), nil
}

func popCount(x uint) int {
	count := 0
	for x > 0 {
		count++
		x &= x - 1
	}
	return count
}

func (s *joinReorderDPSolver) newJoinWithEdge(leftPlan, rightPlan LogicalPlan, edges []joinGroupEqEdge, otherConds []expression.Expression) (LogicalPlan, error) {
	var eqConds []*expression.ScalarFunction
	for _, edge := range edges {
		lCol := edge.edge.GetArgs()[0].(*expression.Column)
		rCol := edge.edge.GetArgs()[1].(*expression.Column)
		if leftPlan.Schema().Contains(lCol) {
			eqConds = append(eqConds, edge.edge)
		} else {
			newSf := expression.NewFunctionInternal(s.ctx, ast.EQ, edge.edge.GetType(), rCol, lCol).(*expression.ScalarFunction)
			eqConds = append(eqConds, newSf)
		}
	}
	join := s.newJoin(leftPlan, rightPlan, eqConds, otherConds)
	_, err := join.recursiveDeriveStats()
	return join, err
}

// Make cartesian join as bushy tree.
func (s *joinReorderDPSolver) makeBushyJoin(cartesianJoinGroup []LogicalPlan, otherConds []expression.Expression) LogicalPlan {
	for len(cartesianJoinGroup) > 1 {
		resultJoinGroup := make([]LogicalPlan, 0, len(cartesianJoinGroup))
		for i := 0; i < len(cartesianJoinGroup); i += 2 {
			if i+1 == len(cartesianJoinGroup) {
				resultJoinGroup = append(resultJoinGroup, cartesianJoinGroup[i])
				break
			}
			// TODO:Since the other condition may involve more than two tables, e.g. t1.a = t2.b+t3.c.
			//  So We'll need a extra stage to deal with it.
			// Currently, we just add it when building cartesianJoinGroup.
			mergedSchema := expression.MergeSchema(cartesianJoinGroup[i].Schema(), cartesianJoinGroup[i+1].Schema())
			var usedOtherConds []expression.Expression
			otherConds, usedOtherConds = expression.FilterOutInPlace(otherConds, func(expr expression.Expression) bool {
				return expression.ExprFromSchema(expr, mergedSchema)
			})
			resultJoinGroup = append(resultJoinGroup, s.newJoin(cartesianJoinGroup[i], cartesianJoinGroup[i+1], nil, usedOtherConds))
		}
		cartesianJoinGroup = resultJoinGroup
	}
	return cartesianJoinGroup[0]
}

func findNodeIndexInGroup(group []LogicalPlan, col *expression.Column) (int, error) {
	for i, plan := range group {
		if plan.Schema().Contains(col) {
			return i, nil
		}
	}
	return -1, ErrUnknownColumn.GenWithStackByArgs(col, "JOIN REORDER RULE")
}
