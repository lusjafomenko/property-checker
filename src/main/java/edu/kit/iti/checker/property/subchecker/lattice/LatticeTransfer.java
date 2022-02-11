/* This file is part of the Property Checker.
 * Copyright (c) 2021 -- present. Property Checker developers.
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details.
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 */
package edu.kit.iti.checker.property.subchecker.lattice;

import com.sun.tools.javac.tree.JCTree;
import edu.kit.iti.checker.property.printer.SMTStringPrinter;
import org.checkerframework.checker.initialization.InitializationTransfer;
import org.checkerframework.dataflow.analysis.TransferInput;
import org.checkerframework.dataflow.analysis.TransferResult;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.framework.type.QualifierHierarchy;

import javax.lang.model.element.VariableElement;
import java.util.ArrayList;

public class LatticeTransfer extends InitializationTransfer<LatticeValue, LatticeTransfer, LatticeStore> {

    //** The Lattice type factory. *//*
    protected final LatticeAnnotatedTypeFactory atypeFactory;

    //** The Lattice type factory. *//*
    protected final QualifierHierarchy hierarchy;

    protected String className = "";

    public LatticeTransfer(LatticeAnalysis analysis) {
        super(analysis);
        atypeFactory = (LatticeAnnotatedTypeFactory) analysis.getTypeFactory();
        hierarchy = atypeFactory.getQualifierHierarchy();
    }

    @Override
    public TransferResult<LatticeValue, LatticeStore> visitAssignment(AssignmentNode n, TransferInput<LatticeValue, LatticeStore> in) {
        TransferResult<LatticeValue, LatticeStore> result = super.visitAssignment(n, in);

        // Lists to collect relative variable names and their values as context;
        ArrayList<String> usedVars = new ArrayList<String>();
        ArrayList<String> relativeValues = new ArrayList<String>();

    //    if (n.getOperands().toArray()[0] instanceof LocalVariableNode) {
    //        System.out.println("local variable " + n.getOperands().toArray()[0]);
    //        if (n.getBlock() != null) {
    //            System.out.println(n.getBlock().getNodes());
    //            List<Node> nodes = n.getBlock().getNodes();
    //            for (Node nod : nodes) {
    //                //System.out.println(nod.getAssignmentContext());
    //                System.out.println(nod.toString() + " ::::" + nod.getType());
    //            }
    //        }
    //    }
        // by class vars "FieldAccessNode"
        //System.out.println(n.getOperands().toArray()[0].getClass());

        // The name of variable (for the moment without (this).);
        String varName = removeThisFromString(n.getTarget().toString());

        JCTree.JCVariableDecl varDec = null;
        JCTree.JCAssign varAssign = null;

        // JCTree to translate to SMT-lib, if method invocation assigned - nothing;
        if (n.getTree().getClass().equals(JCTree.JCVariableDecl.class)) {
            varDec = (JCTree.JCVariableDecl) n.getTree();
        } else {
            varAssign = (JCTree.JCAssign) n.getTree();
        }
        if (varDec != null && varDec.init.getClass().equals(JCTree.JCMethodInvocation.class)) {
            return result;
        }
        if (varAssign != null && varAssign.rhs.getClass().equals(JCTree.JCMethodInvocation.class)) {
            System.out.println("assignement method invocation");
            visitMethodInvocation((MethodInvocationNode) n.getOperands().toArray()[1], in);
            return result;
        }

        // SMTStringPrinter to translate the common assignement to SMT-lib assertion
        SMTStringPrinter printer = new SMTStringPrinter();
        if (varDec != null) {
            relativeValues.add(printer.printVarDec(varDec));
        } else if (varAssign != null) {
            relativeValues.add(printer.printVarAssign(varAssign));
        }

        // check if variable depends on other variables, add them to the context;
        checkExpression(n.getExpression(), relativeValues, usedVars);

        // assume the variable can have only one annotation if any;
        if (!n.getTarget().getType().getAnnotationMirrors().isEmpty()) {

            // add annotated type of the variable to the context;
            String typeWithVarName = getAnnotationFromType(n.getTarget().getType().getAnnotationMirrors().get(0).toString(), varName);
            if (!relativeValues.contains(typeWithVarName)) {
                relativeValues.add(typeWithVarName);
            }

            // if annotation arguments are variables add them to the context;
            ArrayList<String> passedAnnoArgs = new ArrayList<String>();
            getPassedArgs(typeWithVarName, passedAnnoArgs);
            if (!passedAnnoArgs.isEmpty()) {
                for (String a : passedAnnoArgs) {
                   parseExprArg(a, relativeValues, usedVars);
                }
            }
        }

        atypeFactory.getChecker().getParentChecker().resultsForVar.put(varName, relativeValues);
        atypeFactory.getChecker().getParentChecker().usedVarForVar.put(varName, usedVars);

        return result;
    }

    @Override
    public TransferResult<LatticeValue, LatticeStore> visitFieldAccess(FieldAccessNode n, TransferInput<LatticeValue, LatticeStore> p) {
        TransferResult<LatticeValue, LatticeStore> result = super.visitFieldAccess(n, p);
        //System.out.println(n.getFieldName());
        //System.out.println(result.toString());
        return result;
    }

    @Override
    public TransferResult<LatticeValue, LatticeStore> visitMethodInvocation(
            MethodInvocationNode n, TransferInput<LatticeValue, LatticeStore> in) {
        TransferResult<LatticeValue, LatticeStore> result = super.visitMethodInvocation(n, in);

        // sout-test
        String target = n.getTarget().toString();
        System.out.println(target + " :: visitMethodInvocation invoked");

        // Lists to collect relative variable names and their values as context;
        ArrayList<String> relativeValues = new ArrayList<String>();
        ArrayList<String> usedVars = new ArrayList<String>();

        //String regex = atypeFactory.getChecker().getQualPackage() + ".";

        // get variable name
        String v = "";
        if (n.getAssignmentContext() != null) {
            if (n.getAssignmentContext().getContextTree() != null) {
                if (n.getAssignmentContext().getContextTree().getClass().equals(JCTree.JCVariableDecl.class)) {
                    JCTree.JCVariableDecl tree = (JCTree.JCVariableDecl) n.getAssignmentContext().getContextTree();
                    v = tree.name.toString();
                    System.out.println("v := " + v);
                }
                if (n.getAssignmentContext().getContextTree().getClass().equals(JCTree.JCAssign.class)) {
                    JCTree.JCAssign tree = (JCTree.JCAssign) n.getAssignmentContext().getContextTree();
                    v = tree.lhs.toString();
                }
            }
        }

        // get method return type and create temp variable
        String methodReturnType = "";
        if (!n.getTarget().getMethod().getReturnType().getAnnotationMirrors().isEmpty()) {
            methodReturnType = n.getTarget().getMethod().getReturnType().getAnnotationMirrors().get(0).toString();
            methodReturnType = getAnnotationFromType(methodReturnType, v);
            methodReturnType = methodReturnType + "TEMP";

            usedVars.add(v + "TEMP");
            relativeValues.add("(assert (= " + v + " " + v + "TEMP" + "))");
            //System.out.println("method return type : " + methodReturnType);
        }
        relativeValues.add(methodReturnType);

        // add annotation arguments of the method return type to the context;
        ArrayList<String> passedAnnoArgs = new ArrayList<String>();
        getPassedArgs(methodReturnType, passedAnnoArgs);
        if (!passedAnnoArgs.isEmpty()) {
            for (String a : passedAnnoArgs) {
                String[] ar = a.split(" ");
                for (String s : ar) {
                    addInfoToContext(s, relativeValues, usedVars);
                }
            }
        }

        if (!n.getOperands().isEmpty() && (n.getOperands().size() > 1)) {
            // get actual method parameters;
            ArrayList<Node> operands = (ArrayList<Node>) n.getOperands();
            String[] operandsList = new String[operands.size() - 1];
            for (int i = 1; i < operands.size(); i++) {
                operandsList[i-1] = operands.get(i).toString();
            }

            if (!n.getTarget().getMethod().getParameters().isEmpty()) {
                ArrayList<String> parNames = new ArrayList<String>();

                // get method's parameter names;
                for (VariableElement p : n.getTarget().getMethod().getParameters()) {
                    if (!usedVars.contains(p.toString())) {
                        usedVars.add(p.toString());
                    }
                    parNames.add(p.toString());

                    // add method's parameter type annotations to the context;
                    if (!p.asType().getAnnotationMirrors().isEmpty()) {
                        String parAnnoType = p.asType().getAnnotationMirrors().get(0).toString();
                        parAnnoType = getAnnotationFromType(parAnnoType, p.toString());
                        if (!relativeValues.contains(parAnnoType)) {
                            relativeValues.add(parAnnoType);
                        }

                        // if annotation arguments are variables add them to the context;
                        ArrayList<String> passedParamsAnnoArgs = new ArrayList<String>();
                        getPassedArgs(parAnnoType, passedParamsAnnoArgs);
                        if (!passedParamsAnnoArgs.isEmpty()) {
                            for (String a : passedParamsAnnoArgs) {
                                parseExprArg(a, relativeValues, usedVars);
                            }
                        }
                    }
                }

                for (int i = 0; i < parNames.size(); i++) {
                    String assertion = "(assert (= " + parNames.get(i) + " " + operandsList[i] + "))";
                    if (!relativeValues.contains(assertion)) {
                        relativeValues.add(assertion);
                    }
                    if (!isNumeric(operandsList[i]) && !usedVars.contains(operandsList[i])) {
                        usedVars.add(operandsList[i]);
                        if (atypeFactory.getChecker().getParentChecker().resultsForVar.containsKey(operandsList[i])) {
                            for (String res : atypeFactory.getChecker().getParentChecker().resultsForVar.get(operandsList[i])) {
                                if (!relativeValues.contains(res)) {
                                    relativeValues.add(res);
                                }
                            }
                        }
                    }
                }
            }
        }

        atypeFactory.getChecker().getParentChecker().resultsForVar.put(v, relativeValues);
        atypeFactory.getChecker().getParentChecker().usedVarForVar.put(v, usedVars);

        return result;
    }

//@Override public TransferResult<LatticeValue, LatticeStore> visitClassName (ClassNameNode n, TransferInput<LatticeValue, LatticeStore> p) {
//    TransferResult<LatticeValue, LatticeStore> result = super.visitClassName(n, p);
//    System.out.println("!!!!!!!!!!!!!!!class");
//    if (n != null) {
//        this.className = n.toString();
//        System.out.println(this.className);
//    }
//    return result;
//}

//    @Override public TransferResult<LatticeValue, LatticeStore> visitClassDeclaration (ClassDeclarationNode n, TransferInput<LatticeValue, LatticeStore> p) {
//        TransferResult<LatticeValue, LatticeStore> result = super.visitClassDeclaration(n, p);
//        System.out.println("!!!!!!!!!!class");
//        if (n.getTree() != null) {
//            this.className = n.getTree().toString();
//            System.out.println(this.className);
//        }
//        return result;
//    }

    // private method to get the variable name without (this). modifier;
    private String removeThisFromString (String in) {
        String regex = "\\(this\\)\\.";
        return in.replaceAll(regex, "");
    }

    private void checkExpression (Node n, ArrayList<String> knowledge, ArrayList<String> vars) {

        if (n instanceof IntegerLiteralNode) return;

        if (n instanceof FieldAccessNode || n instanceof LocalVariableNode) {
            String key = removeThisFromString(n.toString());
            if (!vars.contains(key)) {
                vars.add(key);
            }
            if (atypeFactory.getChecker().getParentChecker().usedVarForVar.containsKey(key)) {
                for (String k : atypeFactory.getChecker().getParentChecker().usedVarForVar.get(key)) {
                    if (!vars.contains(k)) {
                        vars.add(k);
                    }
                }
            }
            if (atypeFactory.getChecker().getParentChecker().resultsForVar.containsKey(key)) {
                for (String res : atypeFactory.getChecker().getParentChecker().resultsForVar.get(key)) {
                    if (!knowledge.contains(res)) {
                        knowledge.add(res);
                    }
                }

            }
            return;
        }

        for (Node n1 : n.getOperands()) {
            checkExpression(n1, knowledge, vars);
        }
    }

    // get arguments passed to the type annotation;
    private void getPassedArgs (String anno, ArrayList<String> passedArgs) {
        if (anno.contains("\"")) {
                String s = anno.substring(anno.indexOf("\"") + 1);
                String rest = s.substring(s.indexOf("\"") + 1);
                s = s.substring(0, s.indexOf("\""));
                passedArgs.add(s);
                getPassedArgs(rest, passedArgs);
        }
    }

    private String getAnnotationFromType (String type, String var) {
        String regex = atypeFactory.getChecker().getQualPackage() + ".";
        return type.replace(regex, "") + " " + var;
    }

    private static boolean isNumeric(String str){
        return str != null && str.matches("[0-9.]+");
    }

    private static boolean isOperand(String str) {
        if (str.equals("*")) return true;
        if (str.equals("/")) return true;
        if (str.equals("+")) return true;
        if (str.equals("-")) return true;
        if (str.equals("%")) return true;
        return false;
    }

    private void parseExprArg(String exprArg, ArrayList<String> knowledge, ArrayList<String> vars) {
        String [] arArgs = exprArg.split(" ");
        for (int i = 0; i < arArgs.length; i++) {
            if (!isNumeric(arArgs[i]) && !isOperand(arArgs[i]))  {
                if (!vars.contains(arArgs[i])) {
                    vars.add(arArgs[i]);
                }
                if (atypeFactory.getChecker().getParentChecker().usedVarForVar.containsKey(arArgs[i])) {
                    for (String k : atypeFactory.getChecker().getParentChecker().usedVarForVar.get(arArgs[i])) {
                        if (!vars.contains(k)) {
                            vars.add(k);
                        }
                    }
                }
                if (atypeFactory.getChecker().getParentChecker().resultsForVar.containsKey(arArgs[i])) {
                    for (String res : atypeFactory.getChecker().getParentChecker().resultsForVar.get(arArgs[i])) {
                        if (!knowledge.contains(res)) {
                            knowledge.add(res);
                        }
                    }
                    return;
                }
            }
        }
    }

    private void addInfoToContext (String s, ArrayList<String> relativeValues, ArrayList<String> usedVars) {
        if (atypeFactory.getChecker().getParentChecker().resultsForVar.containsKey(s)) {
            if (!usedVars.contains(s)) {
                usedVars.add(s);
            }
            for (String res : atypeFactory.getChecker().getParentChecker().resultsForVar.get((s))) {
                if (!relativeValues.contains(res)) {
                    relativeValues.add(res);
                }
            }
            for (String sv : atypeFactory.getChecker().getParentChecker().usedVarForVar.get(s)) {
                if (!usedVars.contains(sv)) {
                    usedVars.add(sv);
                }
            }
            //    usedVars.addAll(atypeFactory.getChecker().getParentChecker().usedVarForVar.get(s));
        }
    }
}
