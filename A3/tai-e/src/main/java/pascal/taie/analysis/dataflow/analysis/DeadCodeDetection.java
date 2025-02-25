/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode

        for(Stmt stmt:cfg){
            if (stmt instanceof AssignStmt<?,?>){
                RValue rv = ((AssignStmt<?, ?>) stmt).getRValue();
                LValue lv = ((AssignStmt<?, ?>) stmt).getLValue();

                if (lv instanceof Var){
                    if(!liveVars.getResult(stmt).contains((Var)lv)){
                        if (hasNoSideEffect(rv)){
                            deadCode.add(stmt);
                        }
                    }
                }
            }
        }

        Queue<Stmt> queue = new LinkedList<Stmt>();
        Set<Stmt> reachedCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        reachedCode.add(cfg.getEntry());
        reachedCode.add(cfg.getExit());
        queue.add(cfg.getEntry());
        while (!queue.isEmpty()){
            Stmt stmt = queue.poll();
            if (stmt instanceof If){
                ConditionExp condexp = ((If) stmt).getCondition();
                Value condvar = ConstantPropagation.evaluate(condexp,constants.getInFact(stmt));
                if (condvar.isConstant()){
                    Set<Edge<Stmt>> edges = cfg.getOutEdgesOf(stmt);
                    for(Edge edge:edges){
                        if (condvar.getConstant()==1) {
                            if (edge.getKind() == Edge.Kind.IF_TRUE) {
                                if (!reachedCode.contains(edge.getTarget())) {
                                    reachedCode.add((Stmt) edge.getTarget());
                                    queue.add((Stmt) edge.getTarget());
                                }
                                break;
                            }
                        }
                        else if (condvar.getConstant()==0){
                            if(edge.getKind() == Edge.Kind.IF_FALSE){
                                if (!reachedCode.contains(edge.getTarget())){
                                    reachedCode.add((Stmt) edge.getTarget());
                                    queue.add((Stmt) edge.getTarget());
                                }
                                break;
                            }
                        }
                    }
                    continue;
                }
            }
            else if (stmt instanceof SwitchStmt){
                Var switch_var = ((SwitchStmt) stmt).getVar();
                Value switch_value = ConstantPropagation.evaluate(switch_var,constants.getInFact(stmt));

                if (switch_value.isConstant()){
                    for (int casev: ((SwitchStmt) stmt).getCaseValues()){
                        if (casev==switch_value.getConstant()){
                            if (!reachedCode.contains(((SwitchStmt) stmt).getTarget(((SwitchStmt) stmt).getCaseValues().indexOf(casev)))){
                                reachedCode.add(((SwitchStmt) stmt).getTarget(((SwitchStmt) stmt).getCaseValues().indexOf(casev)));
                                queue.add(((SwitchStmt) stmt).getTarget(((SwitchStmt) stmt).getCaseValues().indexOf(casev)));
                            }
                            break;
                        }
                    }
                    if (!((SwitchStmt) stmt).getCaseValues().contains(switch_value.getConstant())){
                        if(!reachedCode.contains( ((SwitchStmt) stmt).getDefaultTarget())){
                            reachedCode.add(((SwitchStmt) stmt).getDefaultTarget());
                            queue.add(((SwitchStmt) stmt).getDefaultTarget());
                        }
                    }
                    continue;
                }
            }
            for(Stmt succ: cfg.getSuccsOf(stmt) ){
                if (!reachedCode.contains(succ)){
                    reachedCode.add(succ);
                    queue.add(succ);
                }
            }
        }

        for(Stmt code: cfg){
            if (!reachedCode.contains(code)){
                deadCode.add(code);
            }
        }

        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
