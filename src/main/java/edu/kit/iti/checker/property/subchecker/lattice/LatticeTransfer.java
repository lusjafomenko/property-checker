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

        ArrayList<String> relativeValues = new ArrayList<String>();
        ArrayList<String> usedVars = new ArrayList<String>();
        String varName = n.getTarget().toString();


       // Long c = result.getRegularStore().getUid();
       // if (c != null) {
       //     System.out.println();
       //     System.out.println(varName + " " + this.className);
       // }

       // Tree tree = n.getTree();
       // if (tree != null) {
       //     ClassTree clTree = (ClassTree) this.analysis.getContainingClass(tree);
       //     if (clTree != null) {
       //         System.out.println(clTree.toString());
       //     }
       // }

        if (varName.contains(".")) {
            varName = varName.substring(varName.indexOf(".") + 1);
        }
        JCTree.JCVariableDecl varDec = (JCTree.JCVariableDecl) n.getTree();
        if (varDec.init.getClass().equals(JCTree.JCMethodInvocation.class)) {
    //        System.out.println(varName + " after visit var ::" + atypeFactory.getChecker().getParentChecker().resultsForVar.get(varName));
            return result;
        }
        //System.out.println(varDec.init.getClass());
        ///!!!!System.out.println(varDec.init.getStartPosition());
        SMTStringPrinter printer = new SMTStringPrinter();
        relativeValues.add(printer.printVarDec(varDec));
        checkExpression(n.getExpression(), relativeValues, usedVars);


        if (!n.getTarget().getType().getAnnotationMirrors().isEmpty()) {

            String targetTypeMirror = n.getTarget().getType().getAnnotationMirrors().get(0).toString();

            String typeWithVarName = getAnnotationFromType(targetTypeMirror, varName);
            //System.out.println(typeWithVarName);

            ArrayList<String> passedAnnoArgs = new ArrayList<String>();
            getPassedArgs(typeWithVarName, passedAnnoArgs);
            if (!passedAnnoArgs.isEmpty()) {
                for (String a : passedAnnoArgs) {
                    if (atypeFactory.getChecker().getParentChecker().resultsForVar.containsKey(a)) {
                        if (!usedVars.contains(a)) {
                            usedVars.add(a);
                        }
                        relativeValues.addAll(atypeFactory.getChecker().getParentChecker().resultsForVar.get(a));
                        for (String v : atypeFactory.getChecker().getParentChecker().usedVarForVar.get(a)) {
                            if (!usedVars.contains(v)) {
                                usedVars.add(v);
                            }
                        }
                        //usedVars.addAll(atypeFactory.getChecker().getParentChecker().usedVarForVar.get(a));
                    }
                }
            }

            relativeValues.add(typeWithVarName);

            //String ident = anType.substring(anType.indexOf("@") + 1, anType.indexOf("("));
        }


        atypeFactory.getChecker().getParentChecker().resultsForVar.put(varName, relativeValues);
        atypeFactory.getChecker().getParentChecker().usedVarForVar.put(varName, usedVars);
    //    System.out.println(varName + " after visit var ::" + relativeValues.toString());
        //System.out.println(usedVars);

        //atypeFactory.getChecker().getParentChecker().transferResultStrings.add(n.toString());
        //if (!n.getTarget().getType().getAnnotationMirrors().isEmpty()) {
        //    atypeFactory.getChecker().getParentChecker().transferResultStrings.add(n.getType().toString());
        //}

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
        //System.out.println(result.getRegularStore().toString());
        //System.out.println(result.getResultValue().toString());
        ArrayList<String> relativeValues = new ArrayList<String>();
        ArrayList<String> usedVars = new ArrayList<String>();
        String v = "";
        String methodReturnType = "";
        String regex = atypeFactory.getChecker().getQualPackage() + ".";
        if (n.getAssignmentContext() != null) {
            if (n.getAssignmentContext().getContextTree() != null) {
    //            System.out.println(n.getAssignmentContext().getContextTree());
    //            System.out.println(n.getAssignmentContext().getContextTree().getClass());
                if (n.getAssignmentContext().getContextTree().getClass().equals(JCTree.JCVariableDecl.class)) {
                    JCTree.JCVariableDecl tree = (JCTree.JCVariableDecl) n.getAssignmentContext().getContextTree();
                    v = tree.name.toString();
    //                System.out.println("v := " + v);
                }
            }
        }

        if (!n.getTarget().getMethod().getReturnType().getAnnotationMirrors().isEmpty()) {
            methodReturnType = n.getTarget().getMethod().getReturnType().getAnnotationMirrors().get(0).toString();
            methodReturnType = getAnnotationFromType(methodReturnType, v);
            methodReturnType = methodReturnType + "TEMP";

            usedVars.add(v + "TEMP");
            relativeValues.add("(assert (= " + v + " " + v + "TEMP" + "))");
            //methodReturnType = methodReturnType.replace(regex, "");
            //methodReturnType = methodReturnType + " " + v;
            //System.out.println("method return type : " + methodReturnType);
        }

        relativeValues.add(methodReturnType);

        ArrayList<String> passedAnnoArgs = new ArrayList<String>();
        getPassedArgs(methodReturnType, passedAnnoArgs);
        if (!passedAnnoArgs.isEmpty()) {
            for (String a : passedAnnoArgs) {
                String[] ar = a.split(" ");
                for (String s : ar) {
                    if (atypeFactory.getChecker().getParentChecker().resultsForVar.containsKey(s)) {
                        if (!usedVars.contains(s)) {
                            usedVars.add(s);
                        }
                        relativeValues.addAll(atypeFactory.getChecker().getParentChecker().resultsForVar.get(s));
                        for (String sv : atypeFactory.getChecker().getParentChecker().usedVarForVar.get(s)) {
                            if (!usedVars.contains(sv)) {
                                usedVars.add(sv);
                            }
                        }
                    //    usedVars.addAll(atypeFactory.getChecker().getParentChecker().usedVarForVar.get(s));
                    }
                }
            }
        }
        //methodReturnType = n.getTarget().getMethod().getReturnType().toString();
        //methodReturnType = methodReturnType.replace(regex, "");
        //System.out.println("method return type : " + methodReturnType);

    //    System.out.println(n.getOperands());
        if (!n.getOperands().isEmpty() && (n.getOperands().size() > 1)) {
    //        System.out.println("operands:: " + n.getOperands());
            ArrayList<Node> operands = (ArrayList<Node>) n.getOperands();
            String[] operandsList = new String[operands.size() - 1];
            for (int i = 1; i < operands.size(); i++) {
    //            System.out.println("op: " + operands.get(i));
                operandsList[i-1] = operands.get(i).toString();
    //            System.out.println("op: " + operandsList[i-1]);
            }

            if (!n.getTarget().getMethod().getParameters().isEmpty()) {
                //System.out.println("first parameter:: " + n.getTarget().getMethod().getParameters().get(0));//.asType());
                //System.out.println("first parameter:: " + n.getTarget().getMethod().getParameters().get(0).asType().getAnnotationMirrors());
                ArrayList<String> parNames = new ArrayList<String>();

                for (VariableElement p : n.getTarget().getMethod().getParameters()) {
                    if (!usedVars.contains(p.toString())) {
                        usedVars.add(p.toString());
                    }
                    parNames.add(p.toString());
    //                System.out.println("parameter: " + p + " type: " + p.asType());
                    if (!p.asType().getAnnotationMirrors().isEmpty()) {
                        String parAnnoType = p.asType().getAnnotationMirrors().get(0).toString();
                        parAnnoType = getAnnotationFromType(parAnnoType, p.toString());

    //                    System.out.println("parAnnoType:: " + parAnnoType);
                        relativeValues.add(parAnnoType);
                    }
                }

                for (int i = 0; i < parNames.size(); i++) {
                    String assertion = "(assert (= " + parNames.get(i) + " " + operandsList[i] + "))";
                    relativeValues.add(assertion);
                    if (!isNumeric(operandsList[i]) && !usedVars.contains(operandsList[i])) {
                        usedVars.add(operandsList[i]);
                        if (atypeFactory.getChecker().getParentChecker().resultsForVar.containsKey(operandsList[i])) {
                            relativeValues.addAll(atypeFactory.getChecker().getParentChecker().resultsForVar.get(operandsList[i]));
                        }
                    }
                }
            }
        }

    //    System.out.println(n.getTarget().toString());
    //    System.out.println(n.toString());
    //    System.out.println(n.getTarget().getMethod().getReturnType());
    //    System.out.println(n.getTarget().getMethod().getParameters());

        JCTree.JCMethodInvocation tree = (JCTree.JCMethodInvocation) n.getTree();
    //    System.out.println(tree.toString());

        atypeFactory.getChecker().getParentChecker().resultsForVar.put(v, relativeValues);
        atypeFactory.getChecker().getParentChecker().usedVarForVar.put(v, usedVars);
    //    System.out.println(atypeFactory.getChecker().getParentChecker().resultsForVar.get(v));
    //    System.out.println("after method invocation" + atypeFactory.getChecker().getParentChecker().resultsForVar);

        return result;
    }

/**
     * Create a new LatticeTransfer.
     *
//     * @param analysis the corresponding analysis
     *//*
    //public LatticeTransfer(CFAbstractAnalysis<LatticeValue, LatticeStore, LatticeTransfer> analysis) {
    //    super(analysis);
    //    atypeFactory = (LatticeAnnotatedTypeFactory) analysis.getTypeFactory();
    //    hierarchy = atypeFactory.getQualifierHierarchy();
    //}

    enum ComparisonOperators {
        EQUAL,
        NOT_EQUAL,
        GREATER_THAN,
        GREATER_THAN_EQ,
        LESS_THAN,
        LESS_THAN_EQ;
    }



/*
public class LatticeTransfer extends InitializationTransfer {

    protected final LatticeAnnotatedTypeFactory aTypeFactory;

    protected final QualifierHierarchy hierarchy;

    public LatticeTransfer(LatticeAnalysis analysis) {
        super(analysis);
        aTypeFactory = (LatticeAnnotatedTypeFactory) analysis.getTypeFactory();
        hierarchy = aTypeFactory.getQualifierHierarchy();
    }*/

//@Override public TransferResult<LatticeValue, LatticeStore> visitClassName (ClassNameNode n, TransferInput<LatticeValue, LatticeStore> p) {
//    TransferResult<LatticeValue, LatticeStore> result = super.visitClassName(n, p);
//    System.out.println("class");
//    this.className = n.toString();
//    return result;
//}

//    @Override public TransferResult<LatticeValue, LatticeStore> visitClassDeclaration (ClassDeclarationNode n, TransferInput<LatticeValue, LatticeStore> p) {
//        TransferResult<LatticeValue, LatticeStore> result = super.visitClassDeclaration(n, p);
//        System.out.println("class");
//        this.className = n.getTree().toString();
//        return result;
//    }

    private String removeThisFromString (String in) {
        //String out = in.replaceAll("\\p{P}","");
        //String regex = "this";
        //if (out.contains(regex)) return out.replaceAll(regex, "");
        //return in;
        //String target = in.copyValueOf("\\(" + "this).".toCharArray());
        String regex = "\\(this\\)\\.";
        return in.replaceAll(regex, "");
    }

    private void checkExpression (Node n, ArrayList<String> knowledge, ArrayList<String> vars) {
        if (n instanceof IntegerLiteralNode) return;
        if (n instanceof FieldAccessNode) {
            String key = removeThisFromString(n.toString());
            vars.add(key);
            if (atypeFactory.getChecker().getParentChecker().resultsForVar.containsKey(key)) {
                knowledge.addAll(atypeFactory.getChecker().getParentChecker().resultsForVar.get(key));
                return;
            }
        }
        for (Node n1 : n.getOperands()) {
            checkExpression(n1, knowledge, vars);
        }
    }

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
}
