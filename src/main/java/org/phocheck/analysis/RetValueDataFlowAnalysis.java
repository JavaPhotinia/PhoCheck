package org.phocheck.analysis;

import soot.Body;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JReturnStmt;

import java.util.*;

public class RetValueDataFlowAnalysis {
    public boolean checkReturnValue(Stack<SootMethod> sootMethodStack) {
        if (!sootMethodStack.isEmpty()) {
            String per = sootMethodStack.pop().getName();
            Set<String> tmpRetVarSet = new HashSet<>();
            boolean flag = false;
            while (!sootMethodStack.isEmpty()) {
                SootMethod current = sootMethodStack.pop();
                if (current.isAbstract()) {
                    per = current.getName();
                    continue;
                }
                Body body = current.retrieveActiveBody();
                Collection<Unit> units = body.getUnits();
                ArrayList<Unit> unitList = new ArrayList<>(units);
                tmpRetVarSet.clear();
                for (Unit unit : unitList) {
                    Stmt stmt = (Stmt) unit;
                    if (stmt instanceof JAssignStmt) {
                        JAssignStmt jAssignStmt = (JAssignStmt) stmt;
                        Value rightVal = jAssignStmt.rightBox.getValue();
                        Value leftVal = jAssignStmt.leftBox.getValue();
                        String strright = rightVal.toString();
                        if (rightVal instanceof InvokeExpr &&  ((InvokeExpr)rightVal).getMethod().getName().equals(per)) {
                            tmpRetVarSet.add(leftVal.toString());
                        } else {
                            for (String s : tmpRetVarSet) {
                                if (strright.contains(s)) {
                                    tmpRetVarSet.add(leftVal.toString());
                                    break;
                                }
                            }
                        }
                    } else if (stmt instanceof JInvokeStmt) {
                        JInvokeStmt jInvokeStmt = (JInvokeStmt) stmt;
                        Value invokeExpr = jInvokeStmt.getInvokeExprBox().getValue();
                        if (invokeExpr instanceof InstanceInvokeExpr) {
                            InstanceInvokeExpr instanceInvokeExpr = (InstanceInvokeExpr) invokeExpr;
                            for (Value arg : instanceInvokeExpr.getArgs()) {
                                if (tmpRetVarSet.contains(arg.toString())) {
                                    tmpRetVarSet.add(instanceInvokeExpr.getBase().toString());
                                    break;
                                }
                            }
                        }
                        if (isModelMethod(jInvokeStmt.getInvokeExpr().getMethod())) {
                            flag = true;
                            break;
                        }
                    } else if (stmt instanceof JReturnStmt) {
                        JReturnStmt jReturnStmt = (JReturnStmt) stmt;
                        String s = jReturnStmt.getOp().toString();
                        if (tmpRetVarSet.contains(s)) {
                            flag = true;
                            break;
                        }
                    }
                }
                if (!flag) break;
                if (!current.getDeclaringClass().getName().contains("Controller")) {
                    flag = false;
                    per = current.getName();
                } else {
                    break;
                }
            }
            return flag;
        } else {
            return false;
        }

    }

    private boolean isModelMethod(SootMethod sootMethod) {
        if (sootMethod.getDeclaringClass().getName().contains("org.springframework.ui.Model") && sootMethod.getName().contains("addAttribute")) {
            return true;
        }
        return false;
    }
}
