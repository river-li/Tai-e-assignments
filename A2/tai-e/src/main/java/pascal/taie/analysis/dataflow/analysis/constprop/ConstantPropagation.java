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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.security.AlgorithmConstraints;
import java.util.List;
import java.util.Optional;
import java.util.Set;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact result = new CPFact();
        List<Var> vars = cfg.getIR().getParams();
        for(Var var:vars){
            if(canHoldInt(var))
                result.update(var, Value.getNAC());
        }
        return result;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        fact.keySet().forEach((key)->{
            target.update(key, meetValue(fact.get(key), target.get(key)));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v2.isNAC() || v1.isNAC()){
            return Value.getNAC();
        }
        else{
            if(v1.isUndef()){
                return Value.makeConstant(v2.getConstant());
            } else if (v2.isUndef()) {
                return Value.makeConstant(v1.getConstant());
            } else {
                if (v1.getConstant()==v2.getConstant()){
                    return Value.makeConstant(v1.getConstant());
                }
                else{
                    return Value.getNAC();
                }
            }
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        if (stmt instanceof DefinitionStmt<?,?>){
            LValue lv = ((DefinitionStmt<?, ?>) stmt).getLValue();
            RValue rv = ((DefinitionStmt<?, ?>) stmt).getRValue();

            if(lv instanceof Var && canHoldInt((Var)lv)){
                CPFact fact = in.copy();
                // 这里之前少了这一句copyFrom(in)，导致实际上没有把in集合的内容加进来
                fact.update((Var)lv, evaluate(rv,in));
                return out.copyFrom(fact);
            }
        }
        return out.copyFrom(in);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        if(exp instanceof IntLiteral){
            // x = c
            return Value.makeConstant(((IntLiteral) exp).getValue());
        }
        else if (exp instanceof Var) {
            // x = y
            return in.get((Var)exp);
        }
        else if (exp instanceof InvokeExp){
            // 这里需要对等号右边是函数调用的情况做处理，否则会在分析interprocedural时出现异常
            return Value.getNAC();
        }
        else if (exp instanceof BinaryExp) {
            BinaryExp.Op op = ((BinaryExp) exp).getOperator();
            Value op1 = in.get(((BinaryExp) exp).getOperand1());
            Value op2 = in.get(((BinaryExp) exp).getOperand2());

            if (op1.isUndef() || op2.isUndef())
                return Value.getUndef();
            else if (op1.isConstant() && op2.isConstant()){
                int op1_cons = op1.getConstant(), op2_cons = op2.getConstant();

                if (exp instanceof ArithmeticExp){
                    if (op == ArithmeticExp.Op.ADD){
                        return Value.makeConstant(op1_cons + op2_cons);
                    }
                    else if (op == ArithmeticExp.Op.SUB){
                        return Value.makeConstant(op1_cons - op2_cons);
                    }
                    else if (op == ArithmeticExp.Op.MUL){
                        return Value.makeConstant(op1_cons * op2_cons);
                    }
                    else if (op == ArithmeticExp.Op.DIV){
                        if (op2_cons!=0)
                            return Value.makeConstant(op1_cons / op2_cons);
                        else
                            return Value.getUndef();
                    }
                    else if (op == ArithmeticExp.Op.REM){
                        if (op2_cons != 0)
                            return Value.makeConstant(op1_cons % op2_cons);
                        else
                            return Value.getUndef();
                    }
                }

                else if (exp instanceof BitwiseExp){
                    if (op == BitwiseExp.Op.OR){
                        return Value.makeConstant(op1_cons | op2_cons);
                    }
                    else if (op == BitwiseExp.Op.AND){
                        return Value.makeConstant(op1_cons & op2_cons);
                    }
                    else if (op == BitwiseExp.Op.XOR){
                        return Value.makeConstant(op1_cons ^ op2_cons);
                    }
                }

                else if (exp instanceof ConditionExp){
                    if (op == ConditionExp.Op.EQ)
                        return Value.makeConstant((op1_cons == op2_cons)?1:0);
                    else if (op == ConditionExp.Op.GE)
                        return Value.makeConstant((op1_cons >= op2_cons)?1:0);
                    else if (op == ConditionExp.Op.GT)
                        return Value.makeConstant((op1_cons > op2_cons)?1:0);
                    else if (op == ConditionExp.Op.LE)
                        return Value.makeConstant((op1_cons <= op2_cons)?1:0);
                    else if (op == ConditionExp.Op.LT)
                        return Value.makeConstant((op1_cons < op2_cons)?1:0);
                    else if (op == ConditionExp.Op.NE)
                        return Value.makeConstant((op1_cons != op2_cons)?1:0);
                }

                else if (exp instanceof ShiftExp){
                    if (op == ShiftExp.Op.SHL)
                        return Value.makeConstant(op1_cons << op2_cons);
                    else if (op == ShiftExp.Op.SHR)
                        return Value.makeConstant(op1_cons >> op2_cons);
                    else if (op == ShiftExp.Op.USHR)
                        return Value.makeConstant(op1_cons >>> op2_cons);
                }
            }
            else{
                if (op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM){
                    if (op2.isConstant() && op2.getConstant()==0){
                        return Value.getUndef();
                    }
                }

                if (op1.isNAC() || op2.isNAC())
                    return Value.getNAC();
            }
        }
        return Value.getNAC();
    }
}
