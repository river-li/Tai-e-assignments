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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.*;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.LinkedList;
import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if(callGraph.addReachableMethod(method))
        {
            method.getIR().getStmts().forEach(stmt -> {
                stmt.accept(stmtProcessor);
            });
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        LinkedList<Stmt> stmts = new LinkedList<>();
        @Override
        public Void visit(New stmt) {
            Var var = stmt.getLValue();
            workList.addEntry(pointerFlowGraph.getVarPtr(var), new PointsToSet(heapModel.getObj(stmt)));
            visitDefault(stmt);
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            Var lvar = stmt.getLValue();
            Var rvar = stmt.getRValue();
            addPFGEdge(pointerFlowGraph.getVarPtr(rvar),pointerFlowGraph.getVarPtr(lvar));
            visitDefault(stmt);
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            // y = x.f
            JField jfield = stmt.getFieldRef().resolve();
            if (jfield.isStatic()){
                Var var = stmt.getLValue();
                addPFGEdge(pointerFlowGraph.getStaticField(jfield), pointerFlowGraph.getVarPtr(var));
            }
            visitDefault(stmt);
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            // x.f = y
            JField jfield = stmt.getFieldRef().resolve();
            if (jfield.isStatic()){
                Var var = stmt.getRValue();
                addPFGEdge(pointerFlowGraph.getVarPtr(var), pointerFlowGraph.getStaticField(jfield));
            }
            visitDefault(stmt);
            return null;
        }

        @Override
        public Void visit(Invoke stmt){
            if (stmt.isStatic()){
                var retvar = stmt.getResult();
                JMethod callee = resolveCallee(null, stmt);
                if (callGraph.addEdge(new Edge<>(CallKind.STATIC, stmt, callee))){
                    addReachable(callee);
                    List<Var> args = stmt.getInvokeExp().getArgs();
                    IR ir = callee.getIR();
                    List<Var> params = ir.getParams();
                    for (int i=0; i<args.size(); i++){
                        addPFGEdge(pointerFlowGraph.getVarPtr(args.get(i)), pointerFlowGraph.getVarPtr(params.get(i)));
                    }
                    if (retvar != null){
                        VarPtr retvarptr = pointerFlowGraph.getVarPtr(retvar);
                        ir.getReturnVars().forEach(var -> {
                            addPFGEdge(pointerFlowGraph.getVarPtr(var), retvarptr);
                        });
                    }
                }
            }
            visitDefault(stmt);
            return null;
        }

        @Override
        public Void visitDefault(Stmt stmt) {
            stmts.add(stmt);
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target)){
            PointsToSet pt = source.getPointsToSet();
            if (!pt.isEmpty())
                workList.addEntry(target, pt);
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()){
            WorkList.Entry entry = workList.pollEntry();
            Pointer ptr = entry.pointer();
            PointsToSet pts = entry.pointsToSet();
            PointsToSet delta = propagate(ptr, pts);

            if(ptr instanceof VarPtr varptr){
                Var var = varptr.getVar();
                delta.forEach(obj -> {
                    // x.f = y
                    var.getStoreFields().stream().filter(storeField -> !storeField.isStatic()).forEach(storeField -> {
                        addPFGEdge(pointerFlowGraph.getVarPtr(storeField.getRValue()), pointerFlowGraph.getInstanceField(obj, storeField.getFieldRef().resolve()));
                    });
                    // y = x.f
                    var.getLoadFields().stream().filter(loadField -> !loadField.isStatic()).forEach(loadField -> {
                        addPFGEdge(pointerFlowGraph.getInstanceField(obj, loadField.getFieldRef().resolve()), pointerFlowGraph.getVarPtr(loadField.getLValue()));
                    });
                    // x[] = y
                    var.getStoreArrays().forEach(storeArray -> {
                        addPFGEdge(pointerFlowGraph.getVarPtr(storeArray.getRValue()), pointerFlowGraph.getArrayIndex(obj));
                    });
                    // y = x[]
                    var.getLoadArrays().forEach(loadArray -> {
                        addPFGEdge(pointerFlowGraph.getArrayIndex(obj), pointerFlowGraph.getVarPtr(loadArray.getLValue()));
                    });
                    // call
                    processCall(var, obj);
                });
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet delta = new PointsToSet();
        if (!pointsToSet.isEmpty()){
            PointsToSet ptn = pointer.getPointsToSet();
            pointsToSet.objects().filter(obj -> !ptn.contains(obj)).forEach(delta::addObject);
            // delta = pts - ptn

            delta.objects().forEach(ptn::addObject);
            pointerFlowGraph.getSuccsOf(pointer).forEach(succ -> workList.addEntry(succ, delta));
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        var.getInvokes().stream().filter(invoke -> !invoke.isStatic()).forEach(invoke -> {
            JMethod method = resolveCallee(recv, invoke);
            // dispatch
            IR ir = method.getIR();

            workList.addEntry(pointerFlowGraph.getVarPtr(ir.getThis()), new PointsToSet(recv));
            if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, method))){
                addReachable(method);
                List<Var> params = ir.getParams();
                List<Var> args = invoke.getInvokeExp().getArgs();
                for (int i=0; i<args.size(); i++){
                    addPFGEdge(pointerFlowGraph.getVarPtr(args.get(i)), pointerFlowGraph.getVarPtr(params.get(i)));
                }
                Var retvar = invoke.getResult();
                if (retvar != null){
                    VarPtr retvarptr = pointerFlowGraph.getVarPtr(retvar);
                    ir.getReturnVars().forEach(var1 -> {
                        addPFGEdge(pointerFlowGraph.getVarPtr(var1), retvarptr);
                    });
                }
            }
        });
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
