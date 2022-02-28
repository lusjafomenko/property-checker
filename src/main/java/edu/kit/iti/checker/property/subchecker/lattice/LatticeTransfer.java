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

import java.util.ArrayList;

public class LatticeTransfer extends InitializationTransfer<LatticeValue, LatticeTransfer, LatticeStore> {

    protected final LatticeAnnotatedTypeFactory atypeFactory;

    public LatticeTransfer(LatticeAnalysis analysis) {
        super(analysis);
        atypeFactory = (LatticeAnnotatedTypeFactory) analysis.getTypeFactory();
    }


    @Override
    public TransferResult<LatticeValue, LatticeStore> visitAssignment(AssignmentNode n, TransferInput<LatticeValue, LatticeStore> in) {
        TransferResult<LatticeValue, LatticeStore> result = super.visitAssignment(n, in);
        //System.out.println("ASSIGNMENT IN TRANSFER :: " + n.getTarget());

        ArrayList<String> usedVars = new ArrayList<String>();
        ArrayList<String> relativeValues = new ArrayList<String>();
        JCTree.JCVariableDecl varDec;
        SMTStringPrinter printer = new SMTStringPrinter();

        if (n.getTarget().toString().contains("(this).")) {
            String var = removeThisFromString(n.getTarget().toString());
            if (n.getTree().getClass().equals(JCTree.JCVariableDecl.class)) {
                varDec = (JCTree.JCVariableDecl) n.getTree();
                if (varDec != null) {
                    relativeValues.add(printer.printVarDec(varDec));
                }
                checkExpression(n.getExpression(), relativeValues, usedVars);

                if (!n.getTarget().getType().getAnnotationMirrors().isEmpty()) {

                    // add annotated type of the variable to the context;
                    String typeWithVarName = getAnnotationFromType(n.getTarget().getType().getAnnotationMirrors().get(0).toString(), var);
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
            }

            atypeFactory.getChecker().getParentChecker().fields.put(var, relativeValues);
            atypeFactory.getChecker().getParentChecker().fieldsUsedVars.put(var, usedVars);
            //System.out.println("MY TARGET :: " + removeThisFromString(n.getTarget().toString()));
        }
        //System.out.println(n.getTarget().getType());
        //System.out.println(atypeFactory.getChecker().getParentChecker().fields);
        //System.out.println(atypeFactory.getChecker().getParentChecker().fieldsUsedVars);
        return result;
    }

    private void checkExpression (Node n, ArrayList<String> knowledge, ArrayList<String> vars) {

        if (n instanceof IntegerLiteralNode) return;

        if (n instanceof FieldAccessNode) { // || n instanceof LocalVariableNode) {
            String key = removeThisFromString(n.toString());
            if (!vars.contains(key)) {
                vars.add(key);
            }
            if (atypeFactory.getChecker().getParentChecker().fieldsUsedVars.containsKey(key)) {
                for (String k : atypeFactory.getChecker().getParentChecker().fieldsUsedVars.get(key)) {
                    if (!vars.contains(k)) {
                        vars.add(k);
                    }
                }
            }
            if (atypeFactory.getChecker().getParentChecker().fields.containsKey(key)) {
                for (String res : atypeFactory.getChecker().getParentChecker().fields.get(key)) {
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

    private String getAnnotationFromType (String type, String var) {
        String regex = atypeFactory.getChecker().getQualPackage() + ".";
        return type.replace(regex, "") + " " + var;
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

    private void parseExprArg(String exprArg, ArrayList<String> knowledge, ArrayList<String> vars) {
        String [] arArgs = exprArg.split(" ");
        for (int i = 0; i < arArgs.length; i++) {
            if (!isNumeric(arArgs[i]) && !isOperand(arArgs[i]))  {
                if (!vars.contains(arArgs[i])) {
                    vars.add(arArgs[i]);
                }
                if (atypeFactory.getChecker().getParentChecker().fieldsUsedVars.containsKey(arArgs[i])) {
                    for (String k : atypeFactory.getChecker().getParentChecker().fieldsUsedVars.get(arArgs[i])) {
                        if (!vars.contains(k)) {
                            vars.add(k);
                        }
                    }
                }
                if (atypeFactory.getChecker().getParentChecker().fields.containsKey(arArgs[i])) {
                    for (String res : atypeFactory.getChecker().getParentChecker().fields.get(arArgs[i])) {
                        if (!knowledge.contains(res)) {
                            knowledge.add(res);
                        }
                    }
                    return;
                }
            }
        }
    }


    private String removeThisFromString (String in) {
        String regex = "\\(this\\)\\.";
        return in.replaceAll(regex, "");
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

    @Override
    public TransferResult<LatticeValue, LatticeStore> visitVariableDeclaration(VariableDeclarationNode n, TransferInput<LatticeValue, LatticeStore> in) {
        TransferResult<LatticeValue, LatticeStore> result = super.visitVariableDeclaration(n, in);
        //System.out.println("VARIABLE DECLARATION IN TRANSFER :: " + n);
        return result;
    }

    @Override
    public TransferResult<LatticeValue, LatticeStore> visitImplicitThis(ImplicitThisNode n, TransferInput<LatticeValue, LatticeStore> in) {
        TransferResult<LatticeValue, LatticeStore> result = super.visitImplicitThis(n, in);
        //System.out.println("IMPLICIT THIS :: " + n);
        return result;
    }

    @Override
    public TransferResult<LatticeValue, LatticeStore> visitExplicitThis(ExplicitThisNode n, TransferInput<LatticeValue, LatticeStore> in) {
        TransferResult<LatticeValue, LatticeStore> result = super.visitExplicitThis(n, in);
        //System.out.println("EXPLICIT THIS :: " + n);
        return result;
    }

    @Override
    public TransferResult<LatticeValue, LatticeStore> visitFieldAccess(FieldAccessNode n, TransferInput<LatticeValue, LatticeStore> p) {
        TransferResult<LatticeValue, LatticeStore> result = super.visitFieldAccess(n, p);
        //System.out.println("I'm in field access " + n.getTree());// + " " + n.getReceiver().getBlock());
        if (n.getTree() instanceof JCTree.JCFieldAccess) {
            JCTree.JCFieldAccess tree = (JCTree.JCFieldAccess) n.getTree();
            //System.out.println("EXPRESSION :: " + tree.getExpression());
            //System.out.println("SYMBOL :: " + tree.sym);
            //System.out.println(tree.sym.owner);
            //System.out.println("SYMBOL TYPE :: " + tree.sym.type);
        }
        //System.out.println(result.getRegularStore());
        //System.out.println(result.getResultValue().getAnnotations());
        return result;
    }

    @Override
    public TransferResult<LatticeValue, LatticeStore> visitObjectCreation(ObjectCreationNode n, TransferInput<LatticeValue, LatticeStore> p) {
        TransferResult<LatticeValue, LatticeStore> result = super.visitObjectCreation(n, p);
        //System.out.println("OBJECT CREATION :: " + n);
        if (n.getAssignmentContext() != null) {
            //System.out.println("ASSIGNMENT CONTEXT :: " + n.getAssignmentContext().getContextTree());
            if (n.getAssignmentContext().getContextTree() instanceof JCTree.JCAssign) {
                //System.out.println("JCAssign");
            }
            if (n.getAssignmentContext().getContextTree() instanceof JCTree.JCVariableDecl) {
                //System.out.println("VarDec");
                JCTree.JCVariableDecl varDec = (JCTree.JCVariableDecl) n.getAssignmentContext().getContextTree();
                //System.out.println("NAME :: " + varDec.name);
            }
        //    System.out.println(n.getAssignmentContext().getElementForType());
        }
        if (n.getTree() instanceof JCTree.JCNewClass) {
            JCTree.JCNewClass tree = (JCTree.JCNewClass) n.getTree();
            //System.out.println("CONSTRUCTOR :: " + tree.constructor.toString());
            //System.out.println("JCNewClass :: " + tree.getIdentifier());
        }
        //System.out.println("OPERANDS OF OBJECT CREATION :: " + n.getOperands());
        //System.out.println("REG STORE :: " + result.getRegularStore());
        return result;
    }

    @Override
    public TransferResult<LatticeValue, LatticeStore> visitMethodInvocation(
            MethodInvocationNode n, TransferInput<LatticeValue, LatticeStore> in) {
        TransferResult<LatticeValue, LatticeStore> result = super.visitMethodInvocation(n, in);
        return result;
    }


}
