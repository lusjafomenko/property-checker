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

import com.sun.source.tree.*;
import com.sun.source.tree.Tree.Kind;
import com.sun.source.util.TreePath;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import edu.kit.iti.checker.property.checker.PropertyChecker;
import edu.kit.iti.checker.property.lattice.EvaluatedPropertyAnnotation;
import edu.kit.iti.checker.property.lattice.Lattice;
import edu.kit.iti.checker.property.lattice.PropertyAnnotation;
import edu.kit.iti.checker.property.lattice.PropertyAnnotationType;
import edu.kit.iti.checker.property.printer.SMTFilePrinter;
import edu.kit.iti.checker.property.printer.SMTStringPrinter;
import edu.kit.iti.checker.property.util.ClassUtils;
import edu.kit.iti.checker.property.util.CollectionUtils;
import edu.kit.iti.checker.property.util.FileUtils;
import edu.kit.iti.checker.property.util.Union;
import org.checkerframework.checker.compilermsgs.qual.CompilerMessageKey;
import org.checkerframework.checker.initialization.InitializationVisitor;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.common.basetype.TypeValidator;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedDeclaredType;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedExecutableType;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.util.AnnotatedTypes;
import org.checkerframework.javacutil.Pair;
import org.checkerframework.javacutil.TreeUtils;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.ExecutableElement;
import javax.lang.model.element.Modifier;
import javax.lang.model.element.Name;
import java.io.*;
import java.nio.file.Paths;
import java.util.*;
import java.util.stream.Collectors;

public class LatticeVisitor extends InitializationVisitor<LatticeAnnotatedTypeFactory, LatticeValue, LatticeStore> {

    private Result result;

    private ClassTree enclClass = null;
    private MethodTree enclMethod = null;
    private boolean enclStaticInitBlock = false;
    private boolean enclInstanceInitBlock = false;
    private String varName = "";
    private boolean isMethodInvocation = false;
    private boolean checkingMethodArgs = false;

    protected LatticeVisitor(BaseTypeChecker checker, LatticeAnnotatedTypeFactory typeFactory) {
        super(checker);

        result = new Result(getLatticeSubchecker());
    }

    public LatticeVisitor(BaseTypeChecker checker) {
        this(checker, null);
    }

    @Override
    public void visit(TreePath path) {
        super.visit(path);

        ((PropertyChecker) checker.getParentChecker()).addResult(getAbsoluteSourceFileName(), result);
    }

    @Override
    public Void visitReturn(ReturnTree node, Void p) {
        this.varName = node.getExpression().toString();

        /////////////////////
        if (enclMethodNameString().equals("<init>")) {
            this.varName = enclClassNameString() + "_" + node.getExpression().toString();
        } else {
            this.varName = enclClassNameString() + enclMethodNameString() + "_" + node.getExpression().toString();
        }
        /////////////////////

        call(() -> super.visitReturn(node, p), () -> result.malTypedReturns.add(node));
        return null;
    }

    @Override
    public Void visitAssignment(AssignmentTree node, Void p) {
        addAssignToContext(node);
        call(() -> super.visitAssignment(node, p), () -> result.malTypedAssignments.add(node));
        return null;
    }

    @Override
    public Void visitNewClass(NewClassTree node, Void p) {
        return super.visitNewClass(node, p);
    }

    @Override
    public Void visitVariable(VariableTree node, Void p) {
        addVarToContext(node);
        PropertyChecker checker = atypeFactory.getChecker().getParentChecker();
        String typeWithVar;
        if (enclMethod == null || enclMethod.toString().equals("<init>")) {
            if (!node.getModifiers().getAnnotations().isEmpty()) {
                for (AnnotationTree at : node.getModifiers().getAnnotations()) {
                    if (!at.getArguments().isEmpty()) {
                        typeWithVar = at.toString() + " " + node.getName().toString();
                        if (!checker.fields.containsKey(node.getName().toString())) {
                            ArrayList<String> res = new ArrayList<String>();
                            res.add(typeWithVar);
                            checker.fields.put(node.getName().toString(), res);
                            checker.fieldsUsedVars.put(node.getName().toString(), new ArrayList<String>());
                        }
                    }
                }
            }
        }

        call(() -> super.visitVariable(node, p), () -> result.malTypedVars.add(node));

        AnnotatedTypeMirror varType = atypeFactory.getAnnotatedTypeLhs(node);

        if (enclMethod == null) {
            if (node.getModifiers().getFlags().contains(Modifier.STATIC)) {
                result.addStaticInvariant(
                        getEnclClassName().toString(),
                        new Invariant(node.getName().toString(), varType));

                if (node.getInitializer() != null) {
                    result.addStaticInitializer(getEnclClassName().toString(), Union.left(node));
                }
            } else {   
            	result.addInstanceInvariant(
            			getEnclClassName().toString(),
            			new Invariant(node.getName().toString(), varType));

            	if (node.getInitializer() != null) {
                    result.addInstanceInitializer(getEnclClassName().toString(), Union.left(node));
                }
            }
        }

        return null;
    }

    @Override
    public void processClassTree(ClassTree classTree) {
        ClassTree prevEnclClass = enclClass;
        enclClass = classTree;

        super.processClassTree(classTree);

        enclClass = prevEnclClass;
    }

    String constructorIdent = null;
    @Override
    public Void visitMethod(MethodTree node, Void p) {

        saveConstructorInfo(node);

        MethodTree prevEnclMethod = enclMethod;
        enclMethod = node;

        if (enclMethodNameString().equals("<init>")) {
            //constructorIdent = enclClassNameString() + enclMethod.getParameters().size();
        } else

        if (!enclMethod.getParameters().isEmpty()) {

            HashMap<String, ArrayList<String>> parameterAnnos = new HashMap<>();
            for (VariableTree parameter : enclMethod.getParameters()) {
                //if (parameter.getType().toString().equals("int")) {
                    String paramName = parameter.getName().toString();
                    parameterAnnos.put(paramName, new ArrayList<>());
                    if (!parameter.getModifiers().getAnnotations().isEmpty()) {
                        for (AnnotationTree anno : parameter.getModifiers().getAnnotations()) {
                            parameterAnnos.get(paramName).add(anno.toString());
                        }
                    }
                //} //else if (!parameter.getModifiers().getAnnotations().isEmpty()) {

                //}
            }
            getLatticeSubchecker().getParentChecker().methodParam.put(enclMethod.getName().toString(), parameterAnnos);
            //System.out.println(getLatticeSubchecker().getParentChecker().methodParam);
        }

        ExecutableElement methodElement = TreeUtils.elementFromDeclaration(node);
        Map<AnnotatedDeclaredType, ExecutableElement> overriddenMethods =
                AnnotatedTypes.overriddenMethods(elements, atypeFactory, methodElement);

        result.overriddenMethods.put(node, overriddenMethods.entrySet().stream().map(e -> Pair.of(
                e.getKey(),
                AnnotatedTypes.asMemberOf(
                        types, atypeFactory, e.getKey(), e.getValue())))
        .collect(Collectors.toList()));

        super.visitMethod(node, p);

        enclMethod = prevEnclMethod;

        return null;
    }

    private void saveConstructorInfo (MethodTree node) {

        if (node.getName().toString().equals("<init>")) {
            String constructorName = enclClassNameString() + node.getParameters().size();
            ArrayList<String> consParams = new ArrayList<>();

            if (node.getParameters().size() > 0) {
                for (VariableTree par : node.getParameters()) {
                    String regex = enclClassNameString() + node.getName().toString() + "_" + par.getName();
                    consParams.add(par.toString().replace(par.getName().toString(), regex));
                }
            }
            atypeFactory.getChecker().getParentChecker().constructorParams.put(constructorName, consParams);
        }
    }

    @Override
    public Void visitBlock(BlockTree node, Void p) {
        boolean prevEnclStaticInitBlock = enclStaticInitBlock;
        boolean prevEnclInstanceInitBlock = enclInstanceInitBlock;

    //    List<StatementTree> statementTrees = (List<StatementTree>) node.getStatements();
    //    for (StatementTree st : statementTrees) {
    //        if (st instanceof IfTree) {
    //            System.out.println("condition :: " + ((IfTree) st).getCondition());
    //        }
    //    }

        if (node.isStatic()) {
            enclStaticInitBlock = true;
            result.addStaticInitializer(getEnclClassName().toString(), Union.right(node));
        } else if (enclMethod == null && !enclInstanceInitBlock) {
            enclInstanceInitBlock = true;
            result.addInstanceInitializer(getEnclClassName().toString(), Union.right(node));
        }

        super.visitBlock(node, p);

        enclStaticInitBlock = prevEnclStaticInitBlock;
        enclInstanceInitBlock = prevEnclInstanceInitBlock;

        return null;
    }

    @Override
    public Void visitConditionalExpression(ConditionalExpressionTree node, Void p) {
        return super.visitConditionalExpression(node, p);
    }

    public Name getEnclClassName() {
        return ((JCClassDecl) enclClass).sym.getQualifiedName();
    }

    public Name getEnclMethodNameName() {
        return ((JCMethodDecl) enclMethod).sym.getQualifiedName();
    }

    public LatticeSubchecker getLatticeSubchecker() {
        return (LatticeSubchecker) checker;
    }

    @Override
    protected TypeValidator createTypeValidator() {
        return new LatticeTypeValidator(checker, this, atypeFactory);
    }

    String currentArgValue = null;
    @Override
    protected void checkArguments(
            List<? extends AnnotatedTypeMirror> requiredArgs,
            List<? extends ExpressionTree> passedArgs,
            CharSequence executableName,
            List<?> paramNames) {

        Pair<Tree, AnnotatedTypeMirror> preAssCtxt = visitorState.getAssignmentContext();
        try {
            for (int i = 0; i < requiredArgs.size(); ++i) {
                this.checkingMethodArgs = true;
                visitorState.setAssignmentContext(Pair.of((Tree) null, (AnnotatedTypeMirror) requiredArgs.get(i)));

                final int idx = i;
                this.varName = paramNames.get(i).toString();

                /////////////////////
                //if (enclMethodNameString().equals("<init>")) {
                //    this.varName = enclClassNameString() + "_" + paramNames.get(i).toString();
                //} else {
                //    this.varName = enclClassNameString() + enclMethodNameString() + "_" + paramNames.get(i).toString();
                //}
                if (!enclMethodNameString().equals("<init>")) {
                    this.varName = enclClassNameString() + this.methodName + "_" + paramNames.get(i).toString();
                }
                /////////////////////

                this.currentArgValue = passedArgs.get(i).toString();
                //System.out.println("HERE " + varName);

                call(
                        () -> commonAssignmentCheck(requiredArgs.get(idx), passedArgs.get(idx), "argument.type.incompatible"), //$NON-NLS-1$
                        () -> {
                            Tree leaf = getCurrentPath().getLeaf();
                            if (leaf instanceof MethodInvocationTree) {
                                result.addMalTypedMethodParam((MethodInvocationTree) getCurrentPath().getLeaf(), idx);
                            } else {
                                result.addMalTypedConstructorParam((NewClassTree) getCurrentPath().getLeaf(), idx);
                            }
                        });

                scan(passedArgs.get(i), null);
                this.currentArgValue = null;
                this.checkingMethodArgs = false;
            }
        } finally {
            visitorState.setAssignmentContext(preAssCtxt);
        }
    }

    String methodName = "";
    boolean fielsAccess = false;
    String fieldName = "";
    boolean objectInitialized = false;
    boolean isInt = false;
    @Override
    protected void commonAssignmentCheck(Tree varTree, ExpressionTree valueExp, @CompilerMessageKey String errorKey, Object... extraArgs) {

        if (varTree.getKind().name().equals("VARIABLE")) {
            JCTree.JCVariableDecl var = (JCTree.JCVariableDecl) varTree;
            this.varName = var.getName().toString();
            /////////////////////
            if (enclMethodNameString().equals("<init>")) {
                this.varName = enclClassNameString() + "_" + var.getName().toString();
            } else {
                this.varName = enclClassNameString() + enclMethodNameString() + "_" + var.getName().toString();
            }
            /////////////////////
            if (!var.getType().toString().equals("int")) {
                isInt = false;
                if (valueExp.getKind().name().equals("NEW_CLASS") || atypeFactory.getChecker().getParentChecker().initializedObjects.containsKey(varName)) {
                    objectInitialized = true;
                } else {
                    objectInitialized = false;
                }
            } else {
                isInt = true;
                objectInitialized = false;
            }
            //System.out.println("===" + this.varName);

        } else if (varTree.getKind().name().equals("IDENTIFIER")){
            JCTree.JCIdent var = (JCTree.JCIdent) varTree;
            this.varName = var.getName().toString();
            /////////////////////
            if (enclMethodNameString().equals("<init>")) {
                this.varName = enclClassNameString() + "_" + var.getName().toString();
            } else {
                this.varName = enclClassNameString() + enclMethodNameString() + "_" + var.getName().toString();
            }
            if (var.type.toString().equals("int")) {
                isInt = true;
            } else {
                isInt = false;
            }
            //System.out.println("$$$" + this.varName);
            /////////////////////
        } //else
         if (varTree.getKind().name().equals("MEMBER_SELECT")){
            JCTree.JCFieldAccess var = (JCTree.JCFieldAccess) varTree;
            this.varName = var.name.toString();
             /////////////////////
             if (enclMethodNameString().equals("<init>")) {
                 this.varName = enclClassNameString() + "_" + var.name.toString();
             } else {
                 this.varName = enclClassNameString() + enclMethodNameString() + "_" + var.name.toString();
             }
             if (var.type.toString().equals("int")) {
                 isInt = true;
             } else {
                 isInt = false;
             }

             /////////////////////
        }

         if (valueExp.getKind().name().equals("NEW_CLASS")) {
             //System.out.println("common assignment check new class " + varName + " " + varTree);
             isInt = false;
             //String v = enclClassNameString() + enclMethodNameString() + "_" + varName;
             JCTree.JCVariableDecl var = (JCTree.JCVariableDecl) varTree;
             atypeFactory.getChecker().getParentChecker().initializedObjects.put(varName, var.vartype.toString());
             copyFieldsValues(atypeFactory.getChecker().getParentChecker().resultsForVar1, atypeFactory.getChecker().getParentChecker().objectFields, var);
             copyFieldsValues(atypeFactory.getChecker().getParentChecker().usedVarForVar1, atypeFactory.getChecker().getParentChecker().objectFieldsVars, var);
         }

        if (valueExp.getKind().name().equals("MEMBER_SELECT")) {
            this.fielsAccess = true;
        //    this.fieldName = valueExp.toString().substring(valueExp.toString().indexOf(".") + 1);
        } else {
            this.fielsAccess = false;
        //    this.fieldName = "";
        }

        if (valueExp.getKind().name().equals("METHOD_INVOCATION")) {

            this.isMethodInvocation = true;
            this.methodName = valueExp.toString().substring(0, valueExp.toString().indexOf("("));
            if (valueExp.toString().contains(".")) {
                String k = valueExp.toString().substring(0, valueExp.toString().indexOf("."));
                String objectName = enclClassNameString() + enclMethodNameString() + "_" + k;
                String objectType = "";
                //System.out.println(atypeFactory.getChecker().getParentChecker().initializedObjects);
                if (atypeFactory.getChecker().getParentChecker().initializedObjects.containsKey(objectName)) {
                    objectType = atypeFactory.getChecker().getParentChecker().initializedObjects.get(objectName);
                    //System.out.println(atypeFactory.getChecker().getParentChecker().initializedObjects.get(objectName));
                }
                String toSearch = methodName.replace(k + ".", objectType);
                //System.out.println("to search " + toSearch);
                MethodInvocationTree mit = (MethodInvocationTree) valueExp;
                JCTree.JCMethodInvocation jcmi = (JCTree.JCMethodInvocation) mit;
                //System.out.println(jcmi.type.getAnnotationMirrors());
                if (!jcmi.type.getAnnotationMirrors().isEmpty()) {
                    for (AnnotationMirror am : jcmi.type.getAnnotationMirrors()) {
                        //System.out.println("HERE " + am);
                        ArrayList<String> pass = new ArrayList<>();
                        getPassedArgs(am.toString(), pass);
                        //System.out.println(pass);

                    }
                }
                methodName = toSearch;
            }
            addMethodInvToContext((MethodInvocationTree) valueExp);
        } else {
            this.isMethodInvocation = false;
            this.methodName = "";
        }

        //System.out.println(varName + " " + valueExp.getKind().name());
        super.commonAssignmentCheck(varTree, valueExp, errorKey, extraArgs);
    }

    private void copyFieldsValues(HashMap<String, ArrayList<String>> in, HashMap<String, ArrayList<String>> out, JCTree.JCVariableDecl var) {
        for (Map.Entry<String, ArrayList<String>> entry : in.entrySet()) {
            String identifier = null;
            ArrayList<String> info = null;
            String key = entry.getKey();
            ArrayList<String> value = entry.getValue();
            String regex = var.vartype + "_";
            if (key.contains(regex)) {
                identifier = key.replace(regex, varName + ".");
                info = new ArrayList<>();
                for (String s : value) {
                    String anResult = s.replace(regex, varName + ".");
                    info.add(anResult);
                }
            }
            if (identifier != null && info != null) {
                out.put(identifier, info);
            }
        }
    }

    boolean isNewClass = false;
    @Override
    protected void commonAssignmentCheck(
            AnnotatedTypeMirror varType,
            AnnotatedTypeMirror valueType,
            Tree valueTree,
            @CompilerMessageKey String errorKey,
            Object... extraArgs) {
        commonAssignmentCheckStartDiagnostic(varType, valueType, valueTree);


        if (valueTree.getClass().equals(JCTree.JCNewClass.class)) {
            isNewClass = true;
            //System.out.println("NEW CLASS");
            JCTree.JCNewClass nc = (JCTree.JCNewClass) valueTree;
            String id = nc.constructor.owner.toString().substring(nc.constructor.owner.toString().indexOf(".") + 1) + nc.args.size();
            if (atypeFactory.getChecker().getParentChecker().fieldsInitializations.get(id) != null) {
                for (String s : atypeFactory.getChecker().getParentChecker().fieldsInitializations.get(id)) {
                    String s1 = s.replace(nc.constructor.owner.toString().substring(nc.constructor.owner.toString().indexOf(".") + 1) + "_", varName + ".");
                    for (Map.Entry<String, ArrayList<String>> entry : atypeFactory.getChecker().getParentChecker().objectFields.entrySet()) {
                        String key = entry.getKey();
                        if (s1.contains(key)) {
                            atypeFactory.getChecker().getParentChecker().objectFields.get(key).add(s1);
                            if (nc.args.size() > 0) {
                                ArrayList<String> consPars = atypeFactory.getChecker().getParentChecker().constructorParams.get(id);
                                for (int i = 0; i < consPars.size(); i++) {
                                    String[] array = consPars.get(i).split(" ");
                                    if (s1.contains(array[array.length - 1])) {
                                        //atypeFactory.getChecker().getParentChecker().objectFields.get(key).add(consPars.get(i));
                                        atypeFactory.getChecker().getParentChecker().objectFieldsVars.get(key).add(array[array.length - 1]);
                                        String init = "(assert (= " + array[array.length - 1] + " " + nc.args.get(i) + "))";
                                        if (!isNumeric(nc.args.get(i).toString()))  {
                                            String argName = enclClassNameString() + enclMethodNameString() + "_" + nc.args.get(i);
                                            if (!atypeFactory.getChecker().getParentChecker().resultsForVar1.containsKey(argName)) {
                                                argName = enclClassNameString() + "_" + nc.args.get(i);
                                            }
                                            init = "(assert (= " + array[array.length - 1] + " " + argName + "))";
                                            atypeFactory.getChecker().getParentChecker().objectFieldsVars.get(key).add(argName);
                                            //System.out.println("!!!!!!!!!" + atypeFactory.getChecker().getParentChecker().resultsForVar1.get(argName));
                                            if (atypeFactory.getChecker().getParentChecker().objectFields.containsKey(key)) {
                                                atypeFactory.getChecker().getParentChecker().objectFields.get(key).addAll(atypeFactory.getChecker().getParentChecker().resultsForVar1.get(argName));
                                                atypeFactory.getChecker().getParentChecker().objectFieldsVars.get(key).addAll(atypeFactory.getChecker().getParentChecker().usedVarForVar1.get(argName));
                                            }
                                        }
                                        atypeFactory.getChecker().getParentChecker().objectFields.get(key).add(init);
                                        //System.out.println("RESULTS FOR " + varName + " " + atypeFactory.getChecker().getParentChecker().objectFields.get(key));
                                    }
                                }
                            }
                        }
                        //System.out.println(atypeFactory.getChecker().getParentChecker().objectFields.get(key));
                    }
                }
            }
        } else {
            isNewClass = false;
        }
        AnnotatedTypeMirror widenedValueType = atypeFactory.getWidenedType(valueType, varType);
        PropertyAnnotation pa = getLatticeSubchecker().getTypeFactory().getLattice().getPropertyAnnotation(varType);
        PropertyChecker checker = getLatticeSubchecker().getParentChecker();
        boolean success = atypeFactory.getTypeHierarchy().isSubtype(widenedValueType, varType);

        //if (isInt || objectInitialized) {
            if (!success && valueTree instanceof LiteralTree) {
                LiteralTree literal = (LiteralTree) valueTree;
                EvaluatedPropertyAnnotation epa = getLatticeSubchecker().getTypeFactory().getLattice().getEvaluatedPropertyAnnotation(varType);

                if (epa != null) {
                    PropertyAnnotationType pat = epa.getAnnotationType();
                    Class<?> literalClass = ClassUtils.literalKindToClass(literal.getKind());
                    if (literalClass != null && literalClass.equals(pat.getSubjectType())) {
                        //System.out.println("florians stuff");
                        success = epa.checkProperty(literal.getValue());
                    } else if (literal.getKind() == Kind.NULL_LITERAL && !pat.getSubjectType().isPrimitive()) {
                        //System.out.println("another florians stuff");
                        success = epa.checkProperty(null);
                    }


                } else if (this.checkingMethodArgs) {
                    //System.out.println("checking args and literal");
                    //System.out.println("LITERAL " + varName + " " + currentArgValue);
                    success = checkMethodArgs(checker, pa);

                } else if (!isMethodInvocation) {
                    //System.out.println("not method invocation and literal");
                    addAnnoArgsToContext(pa.getActualParameters());
                    success = SMTcheck(checker, pa);
                }
            } else if (!success) {
                if (fielsAccess) {
                    //System.out.println("not literal and field access");
                    addAnnoArgsToContext(pa.getActualParameters());
                    addFieldInfoToContext(fieldName, checker.resultsForVar1.get(varName), checker.usedVarForVar1.get(varName));
                    success = SMTcheck(checker, pa);
                } else if (this.checkingMethodArgs) {
                    //System.out.println("not literal and checking args");
                    //System.out.println("NOT LITERAL " + varName + " " + currentArgValue + " " + methodName);
                    success = checkMethodArgs(checker, pa);
                } else {
                    //System.out.println("not literal, not fields access, not checking args");
                    //System.out.println(pa.getActualParameters());
                    addAnnoArgsToContext(pa.getActualParameters());
                    success = SMTcheck(checker, pa);
                }

            }
       // }
        commonAssignmentCheckEndDiagnostic(success, null, varType, valueType, valueTree);

        if (!success) {
            super.commonAssignmentCheck(varType, valueType, valueTree, errorKey, extraArgs);
        }

    }


    @Override
    protected void checkMethodInvocability(AnnotatedExecutableType method, MethodInvocationTree node) {
        call(
                () -> super.checkMethodInvocability(method, node),
                () -> result.malTypedMethodReceivers.add(node));
    }

    @Override
    protected void checkSuperConstructorCall(MethodInvocationTree superCall) {
        // Do nothing
    }

    @Override
    protected void checkConstructorResult(
            AnnotatedExecutableType constructorType, ExecutableElement constructorElement) {
        //System.out.println("CONSTRUCTOR " + constructorElement + " " + constructorType);
        QualifierHierarchy qualifierHierarchy = atypeFactory.getQualifierHierarchy();
        Set<AnnotationMirror> constructorAnnotations =
                constructorType.getReturnType().getAnnotations();
        AnnotationMirror top = atypeFactory.getTop();

        AnnotationMirror constructorAnno =
                qualifierHierarchy.findAnnotationInHierarchy(constructorAnnotations, top);
        //System.out.println("CONSTRUCTOR ANNO " + constructorAnno);
        //System.out.println("TOP " + top);
        //System.out.println("COND FOR ERROR " + qualifierHierarchy.isSubtype(top, constructorAnno));
        if (!qualifierHierarchy.isSubtype(top, constructorAnno)) {
            // Report an error instead of a warning.
            checker.reportError(
                    constructorElement, "inconsistent.constructor.type", constructorAnno, top); //$NON-NLS-1$

            result.malTypedConstructors.add(enclMethod);
        }
    }

    protected void call(Runnable callee, Runnable onError) {
        int startErrorCount = getLatticeSubchecker().getErrorCount();
        callee.run();
        int endErrorCount = getLatticeSubchecker().getErrorCount();
        if (startErrorCount < endErrorCount) {
            onError.run();
        }
        getLatticeSubchecker().setErrorCount(startErrorCount);
    }

    protected String getSourceFileName() {
        return root.getSourceFile().getName();
    }

    protected String getAbsoluteSourceFileName() {
        return Paths.get(root.getSourceFile().getName()).toAbsolutePath().toString();
    }

    protected long getStartLineNumber(Tree tree) {
        return root.getLineMap().getLineNumber(positions.getStartPosition(root, tree));
    }

    protected static boolean isConstructor(MethodTree tree) {
        JCMethodDecl t = (JCMethodDecl) tree;
        return t.name == t.name.table.names.init;
    }

    private void printSMT (PropertyChecker checker, File file, PropertyAnnotation pa) {
        String nameToLookup = getNameToLookUp();

        if (checker.resultsForVar1.containsKey(nameToLookup)) {

            try (BufferedWriter outS = new BufferedWriter(new FileWriter(file))) {
                SMTFilePrinter printer = new SMTFilePrinter(outS, checker, varName, enclClassNameString(), enclMethodNameString(), this.methodName, this.checkingMethodArgs, this.fielsAccess, this.isNewClass);
                catchFields(pa.getAnnotationType().getProperty());

                if (checker.usedVarForVar1.containsKey(nameToLookup)) {
                    ArrayList<String> varDecs = checker.usedVarForVar1.get(nameToLookup);
                    for (String v : varDecs) {
                        //////////////////
                        //v = v.substring(v.indexOf("_") + 1);
                        /////////////////
                        printer.print("(declare-const " + v + " Int)");
                        printer.println();
                    }
                }
            //    String f = checkForField(pa.getAnnotationType().getProperty(), varName);
            //    if (f != null) {
            //        printer.print("(declare-const " + f + " Int)");
            //        printer.println();
            //        String field = f.substring(f.indexOf(".") + 1);
            //        if (checker.fields.containsKey(field)) {
            //            for (String r : checker.fields.get(field)) {
            //                String info = r.replace(field, f);
            //                checker.resultsForVar1.get(nameToLookup).add(info);
            //            }
            //        }
            //    }
                printer.print("(declare-const " + varName + " Int)");
                printer.println();
                ArrayList<String> results = checker.resultsForVar1.get(nameToLookup);
                //System.out.println("RESULTS TO PRINT " + nameToLookup + " " + checker.resultsForVar1.get(nameToLookup));
                for (String r : results) {
                    printer.printLine(r);
                }
                printer.printAnnoToProve(pa, varName);
                printer.print("(check-sat)");

            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }

    private void catchFields (String prop) {
        PropertyChecker checker = atypeFactory.getChecker().getParentChecker();
        String[] splitted = prop.split(" ");
        for (int i = 0; i < splitted.length; i++) {
            if (splitted[i].contains("§subject§.")) {
                String field = splitted[i].replace("§subject§", varName);
                if (checker.objectFields.containsKey(field)) {
                    checker.resultsForVar1.get(varName).addAll(checker.objectFields.get(field));
                }
                if (!checker.usedVarForVar1.get(varName).contains(field)) {
                    checker.usedVarForVar1.get(varName).add(field);
                }
                if (checker.objectFieldsVars.containsKey(field)) {
                    for (String f : checker.objectFieldsVars.get(field)) {
                        if (!checker.usedVarForVar1.get(varName).contains(f)) {
                            checker.usedVarForVar1.get(varName).add(f);
                        }
                    }
                }
            }
        }
    }

    private String checkForField(String in, String var) {
        String [] ar = in.split(" ");
        for (String s : ar) {
            if (s.contains(".")) {
                if (s.contains("§subject§")) {
                    return s.replace("§subject§", var);
                }
            }
        }
        return null;
    }

    private boolean checkWithZ3 (String smtName) {
        boolean success = false;
        Runtime runtime = Runtime.getRuntime();
        try {
            Process process = runtime.exec(new String[]{"z3", smtName}, null, new File(getLatticeSubchecker().getParentChecker().getOutputDir()));
            String line;
            InputStream os = process.getInputStream();
            BufferedReader brCleanUp =
                    new BufferedReader(new InputStreamReader(os));

            line = brCleanUp.readLine();
            //System.out.println(varName);
            if (line != null && (line.equals("unsat"))) { //|| line.equals("sat"))) {
                System.out.println(smtName);
                System.out.println("[Stdout] " + line);
            }
            if (line != null) {
                if (line.equals("unsat")) success = true;
            }
            brCleanUp.close();
//                                runtime.exit(0);
        } catch (IOException e) {
            e.printStackTrace();
        }
        return success;
    }

    private boolean SMTcheck (PropertyChecker checker, PropertyAnnotation pa) {
        // create .smt file for the variable
        String smtName = getSMTFileName(varName);
        File file = createSMTFile(smtName);
        printSMT(checker, file, pa);
        return checkWithZ3(smtName);
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

    int count = 0;
    private String getSMTFileName (String varName) {
        //System.out.println("GETTING THE SMT FILE NAME FOR " + varName);
        String smtName = getEnclClassName().toString() + varName + "_" + count + ".smt";
        if (enclMethod != null) {
            smtName = getEnclClassName().toString() + getEnclMethodNameName().toString() + varName + "_" + count + ".smt";
        }

        ///////////////////////////
        smtName = varName + "_" + count + ".smt";
        ///////////////////////////

        count++;
        return smtName;
    }

    private File createSMTFile (String smtName) {
        File file = Paths.get(getLatticeSubchecker().getParentChecker().getOutputDir(), smtName).toFile();
        file.getParentFile().mkdirs();
        FileUtils.createFile(file);
        return file;
    }

    private void parseExprArg1(String exprArg, ArrayList<String> knowledge, ArrayList<String> vars) {
        if (knowledge != null && vars != null) {
            String[] arArgs = exprArg.split(" ");
            for (int i = 0; i < arArgs.length; i++) {
                if (!isNumeric(arArgs[i]) && !isOperand(arArgs[i])) {
                    String argName = "";
                    if (enclMethod != null) {
                        argName = enclClassNameString() + enclMethodNameString() + "_" + arArgs[i];
                        if (!atypeFactory.getChecker().getParentChecker().usedVarForVar1.containsKey(argName)) {
                            argName = enclClassNameString() + "_" + arArgs[i];
                        }
                    } else {
                        argName = enclClassNameString() + "_" + arArgs[i];
                    }

                    if (!vars.contains(argName)) {
                        vars.add(argName);
                    }
                    addInfoToLocalContext(argName, atypeFactory.getChecker().getParentChecker().usedVarForVar1, vars);
                    addInfoToLocalContext(argName, atypeFactory.getChecker().getParentChecker().resultsForVar1, knowledge);
                }
            }
        }
        return;
    }

    private void addInfoToContext (String s, ArrayList<String> relativeValues, ArrayList<String> usedVars) {
        if (atypeFactory.getChecker().getParentChecker().resultsForVar1.containsKey(s)) {
            if (!usedVars.contains(s)) {
                usedVars.add(s);
            }
        }
        //System.out.println("ADD INFO TO CONTEXT");
        addInfoToLocalContext(s, atypeFactory.getChecker().getParentChecker().resultsForVar1, relativeValues);
        addInfoToLocalContext(s, atypeFactory.getChecker().getParentChecker().usedVarForVar1, usedVars);
    }

    private void addAnnoArgsToContext(List<String> annoArgs) {
        if (!annoArgs.isEmpty()) {
            PropertyChecker checker = atypeFactory.getChecker().getParentChecker();
            for (String a : annoArgs) {
                String nameToLookup = getNameToLookUp();
                parseExprArg1(a, checker.resultsForVar1.get(nameToLookup), checker.usedVarForVar1.get(nameToLookup));
            }
        }
    }

    @Override
    public Void visitMethodInvocation (MethodInvocationTree node, Void p) {
        //System.out.println("VISITING METHOD INVOCATION " + node.getMethodSelect());
        //if (node.getMethodSelect().toString().equals("super()")) {
        //    this.methodName = node.getMethodSelect().toString();
        //} else {
        //    this.methodName = "";
        //}
        return super.visitMethodInvocation(node, p);
    }

    private boolean checkMethodArgs (PropertyChecker checker, PropertyAnnotation pa) {

        String v = enclClassNameString() + this.methodName + "_" + varName;

        /////////////////////////////
        v = enclClassNameString() + this.methodName + "_" + varName.substring(varName.indexOf("_") + 1);
        //System.out.println("IN CHECKING METHOD ARGS " + v);
        //System.out.println(pa.getAnnotationType().getProperty());
        //System.out.println(pa.getActualParameters());
        //////////////////////////////////////

        ArrayList<String> tempRelativeValues = new ArrayList<String>();
        ArrayList<String> tempUsedVars = new ArrayList<String>();

        //WARNINGS about Object
        boolean isAbsent = false;
        if (checker.resultsForVar1.get(v) != null) {
            isAbsent = false;
            tempRelativeValues.addAll(checker.resultsForVar1.get(v));
            tempUsedVars.addAll(checker.usedVarForVar1.get(v));
        } else {
            isAbsent = true;
            checker.resultsForVar1.put(v, new ArrayList<String>());
            checker.usedVarForVar1.put(v, new ArrayList<String>());
        }
        //System.out.println(checker.resultsForVar1);

        //String curArgValWithPath = currentArgValue;
        ////////////////////////
        //if (!isInt) {
        //    System.out.println(this.varName);
        //}




        //checker.resultsForVar1.get(v).add("(assert (= " + varName + " " + currentArgValue + "))");
        if (!isNumeric(currentArgValue)) {
            //System.out.println("CURRENT ARG VALUE IS NOT NUMERIC " + currentArgValue);
            String cav = enclClassNameString() + enclMethodNameString() + "_" + currentArgValue;
            if (!checker.resultsForVar1.containsKey(cav)) {
                cav = enclClassNameString() + "_" + currentArgValue;
            }
            //System.out.println("cav :: " + cav);
            for (Map.Entry<String, ArrayList<String>> entry : checker.objectFields.entrySet()) {
                String key = entry.getKey();
                //System.out.println(key);
                if (key.contains(cav)) {
                    if (!checker.usedVarForVar1.get(v).contains(key)) {
                        checker.usedVarForVar1.get(v).add(key);
                    }
                    String field = key.replace(cav, v);
                    if (!checker.usedVarForVar1.get(v).contains(field)) {
                        checker.usedVarForVar1.get(v).add(field);
                    }
                    checker.resultsForVar1.get(v).add("(assert (= " + field + " " + key + "))");
                    //System.out.println(key);
                }
            }
            //System.out.println(checker.initializedObjects.get(cav));



            //System.out.println(cav);
            checker.resultsForVar1.get(v).add("(assert (= " + varName + " " + cav + "))");
            addInfoToContext(cav, checker.resultsForVar1.get(v), checker.usedVarForVar1.get(v));
            //System.out.println(checker.resultsForVar1.get(v));
        } else {
            checker.resultsForVar1.get(v).add("(assert (= " + varName + " " + currentArgValue + "))");
        }

        //System.out.println("HERE");
        boolean success = SMTcheck(checker, pa);

        if (!tempRelativeValues.isEmpty() && !tempUsedVars.isEmpty() && !isAbsent) {
            checker.resultsForVar1.put(v, tempRelativeValues);
            checker.usedVarForVar1.put(v, tempUsedVars);
        } else if (isAbsent) {
            checker.resultsForVar1.remove(v);
            checker.usedVarForVar1.remove(v);
        }

        return success;
    }

    private void checkExpression (JCTree.JCExpression n, ArrayList<String> knowledge, ArrayList<String> vars) {

        if (n instanceof LiteralTree) return;

        if (n instanceof IdentifierTree) {

            String key = enclClassNameString() + enclMethodNameString() + "_" + n.toString();
            if (!atypeFactory.getChecker().getParentChecker().resultsForVar1.containsKey(key)) {
                key = enclClassNameString() + "_" + n.toString();
            }
            if (!vars.contains(key)) {
                vars.add(key);
            }
            addInfoToLocalContext(key, atypeFactory.getChecker().getParentChecker().usedVarForVar1, vars);
            addInfoToLocalContext(key, atypeFactory.getChecker().getParentChecker().resultsForVar1, knowledge);
            return;
        }

        if (n instanceof BinaryTree) {
            checkExpression((JCTree.JCExpression) ((BinaryTree) n).getLeftOperand(), knowledge, vars);
            checkExpression((JCTree.JCExpression) ((BinaryTree) n).getRightOperand(), knowledge, vars);
        }

        if (n instanceof ParenthesizedTree) {
            checkExpression((JCTree.JCExpression) ((ParenthesizedTree) n).getExpression(), knowledge, vars);
        }
    }

    private String enclClassNameString() {
        if (enclClass != null) {
            return enclClass.getSimpleName().toString();
        }
        return "";
    }

    private String enclMethodNameString() {
        if (enclMethod != null) {
            return enclMethod.getName().toString();
        }
        return "";
    }

    private String getAnnotationFromType (String type, String var) {
        String regex = atypeFactory.getChecker().getQualPackage() + ".";
        return type.replace(regex, "") + " " + var;
    }

    String varMethodInvocation = null;
    private void addVarToContext (VariableTree node) {
        PropertyChecker checker = getLatticeSubchecker().getParentChecker();
        // I don't know what happens with varName, so I set it here
        varName = node.getName().toString();

        /////////////////////
        if (enclMethodNameString().equals("<init>")) {
            this.varName = enclClassNameString() + "_" + node.getName().toString();
            //constructorIdent = enclClassNameString() + enclMethod.getParameters().size();
        } else {
            this.varName = enclClassNameString() + enclMethodNameString() + "_" + node.getName().toString();
            //constructorIdent = null;
        }

        /////////////////////


        if (node.getType().toString().equals("int")) {
            String var = enclClassNameString() + enclMethodNameString() + "_" + node.getName().toString();
            ArrayList<String> usedVars = new ArrayList<String>();
            ArrayList<String> relativeValues = new ArrayList<String>();
            JCTree.JCVariableDecl varDec = (JCTree.JCVariableDecl) node;
            String varFieldInit = null;
            SMTStringPrinter printer = new SMTStringPrinter(enclClassNameString(), enclMethodNameString(), this.methodName, this.checkingMethodArgs, checker);
            if (node.getInitializer() instanceof MethodInvocationTree) {
                varMethodInvocation = var;
                return;
            }
            if (node.getInitializer() != null && node.getInitializer().getClass().equals(JCTree.JCFieldAccess.class)) {
                if (enclMethodNameString().equals("<init>")) {
                    fieldName = enclClassNameString() + "_" + node.getInitializer().toString();
                } else {
                    fieldName = enclClassNameString() + enclMethodNameString() + "_" + node.getInitializer().toString();
                }


                relativeValues.add("(assert (= " + varName + " " + fieldName + "))");
                //varFieldInit = "(assert (= " + varName + " " + fieldName + "))";


                if (checker.objectFields.containsKey(fieldName)) {
                    usedVars.add(fieldName);
                    addFieldInfoToContext(fieldName, relativeValues, usedVars);
                }
            } else {
                if (node.getInitializer() != null) {
                    relativeValues.add(printer.printVarDec(varDec));
                }
                checkExpression((JCTree.JCExpression) node.getInitializer(), relativeValues, usedVars);
            }

            //if (varFieldInit != null) {
            //    relativeValues.add(varFieldInit);
            //}

            if (!varDec.mods.annotations.isEmpty()) {
                checker.typeAnnos.put(var, new ArrayList<>());
                for (JCTree.JCAnnotation anno : varDec.mods.annotations) {
                    String typeWithVarName = anno.toString() + " " + varDec.name.toString();
                    checker.typeAnnos.get(var).add(typeWithVarName);
                    if (!relativeValues.contains(typeWithVarName)) relativeValues.add(typeWithVarName);
                    ArrayList<String> passedAnnoArgs = new ArrayList<String>();
                    getPassedArgs(typeWithVarName, passedAnnoArgs);

                    if (!passedAnnoArgs.isEmpty()) {
                        for (String a : passedAnnoArgs) {
                            String[] ar = a.split(" ");
                            for (String s : ar) {
                                if (!isNumeric(s) && !isOperand(s)) {
                                    String s1 = enclClassNameString() + "_" + s;
                                    if (enclMethod != null) {
                                        s1 = enclClassNameString() + enclMethodNameString() + "_" + s;
                                        if (!atypeFactory.getChecker().getParentChecker().resultsForVar1.containsKey(s1)) {
                                            s1 = enclClassNameString() + "_" + s;
                                        }

                                    }
                                    addInfoToContext(s1, relativeValues, usedVars);
                                }
                            }
                        }
                    }
                }
            }


            checker.resultsForVar1.put(var, relativeValues);
            checker.usedVarForVar1.put(var, usedVars);

            if (node.getInitializer() != null && node.getInitializer().getClass().equals(JCTree.JCFieldAccess.class)) {

            }
        } else {
            if (!node.getModifiers().getAnnotations().isEmpty()) {
                boolean hasIntArguments = false;
                ArrayList<String> paramNames = new ArrayList<String>();
                for (AnnotationTree annotTree : node.getModifiers().getAnnotations()) {
                    String annotationType = annotTree.getAnnotationType().toString();

                    if (atypeFactory.getChecker().getTypeFactory().getLattice().getAnnotationTypes().containsKey(annotationType)) {
                        PropertyAnnotationType pat = atypeFactory.getChecker().getTypeFactory().getLattice().getAnnotationTypes().get(annotationType);
                        for (PropertyAnnotationType.Parameter p : pat.getParameters()) {
                            //.println("PAT PARAMETER " + p.getName() + " " + p.getType());
                            if (p.getType().toString().equals("int")) hasIntArguments = true;
                            paramNames.add(p.getName());
                        }
                    }
                    if (hasIntArguments) {
                        ArrayList<String> usedVars = new ArrayList<String>();
                        ArrayList<String> relativeValues = new ArrayList<String>();
                        varName = node.getName().toString();

                        /////////////////////
                        if (enclMethodNameString().equals("<init>")) {
                            this.varName = enclClassNameString() + "_" + node.getName().toString();
                        } else {
                            this.varName = enclClassNameString() + enclMethodNameString() + "_" + node.getName().toString();
                        }
                        /////////////////////

                        String var = enclClassNameString() + enclMethodNameString() + "_" + node.getName().toString();
                        JCTree.JCVariableDecl varDec = (JCTree.JCVariableDecl) node;
                        String typeWithVarName = "";
                        List<JCTree.JCAnnotation> l = varDec.mods.annotations;
                        for (JCTree.JCAnnotation a : l) {
                            if (a.toString().contains(annotTree.getAnnotationType().toString())) {
                                typeWithVarName = a.toString() + " " + varDec.name.toString();
                            }
                        }
                        relativeValues.add(typeWithVarName);
                        ArrayList<String> passedAnnoArgs = new ArrayList<String>();
                        getPassedArgs(typeWithVarName, passedAnnoArgs);
                        if (!passedAnnoArgs.isEmpty()) {
                            for (String a : passedAnnoArgs) {
                                String[] ar = a.split(" ");
                                for (String s : ar) {

                                    if (!isNumeric(s) && !isOperand(s)) {
                                        String s1 = enclClassNameString() + "_" + s;
                                        if (enclMethod != null) {
                                            s1 = enclClassNameString() + enclMethodNameString() + "_" + s;
                                            if (!atypeFactory.getChecker().getParentChecker().resultsForVar1.containsKey(s1)) {
                                                s1 = enclClassNameString() + "_" + s;
                                            }

                                        }
                                        addInfoToContext(s1, relativeValues, usedVars);
                                    }
                                }
                            }
                        }
                        //for (Map.Entry<String, ArrayList<String>> entry : checker.objectFields.entrySet()) {
                        //    String key = entry.getKey();
                        //    if (key.contains(var)) {
                        //        relativeValues.addAll(checker.objectFields.get(key));
                        //        usedVars.addAll(checker.objectFieldsVars.get(key));
                        //    }
                        //}

                        checker.resultsForVar1.put(var, relativeValues);
                        checker.usedVarForVar1.put(var, usedVars);
                    }
                }

                //List<AnnotationTree> annoTree = (List<AnnotationTree>) node.getModifiers().getAnnotations();
            }
        }
    }

    private void saveConstructorAssignments (String varIdent, JCTree.JCAssign node) {
        ArrayList<String> relativeValues = new ArrayList<>();
        JCTree.JCExpression right = node.rhs;
        String value = expToString(right);
        String toAdd = "(assert (= " + varIdent + " " + value + "))";
        relativeValues.add(toAdd);
        if (!atypeFactory.getChecker().getParentChecker().fieldsInitializations.containsKey(constructorIdent)) {
            atypeFactory.getChecker().getParentChecker().fieldsInitializations.put(constructorIdent, relativeValues);
        } else {
            if (!atypeFactory.getChecker().getParentChecker().fieldsInitializations.get(constructorIdent).contains(toAdd)) {
                atypeFactory.getChecker().getParentChecker().fieldsInitializations.get(constructorIdent).add(toAdd);
            }
        }
    }

    private String tagToOp(JCTree.Tag tag) {
        String smt = "";
        switch (tag) {
            case MINUS: smt = "-";
                break;
            case PLUS: smt = "+";
                break;
            case MUL: smt = "*";
                break;
            case DIV: smt = "div";
                break;
            case MOD: smt = "mod";
                break;
            default: break;
        }
        return smt;
    }

    private String expToString (JCTree.JCExpression exp) {
        String smt = "";
        if (exp instanceof LiteralTree) {
            smt = exp.toString();
        } else if (exp instanceof BinaryTree) {
            JCTree.JCBinary tree = (JCTree.JCBinary) exp;
            smt = "(" + tagToOp(exp.getTag()) + " " + expToString(tree.lhs) + " " + expToString(tree.rhs) + ")";
        } else {
            smt = enclClassNameString() + enclMethodNameString() + "_" + exp.toString();
        }
        return smt;
    }

    private void addAssignToContext(AssignmentTree node) {

        if (enclMethodNameString().equals("<init>")) {
            constructorIdent = enclClassNameString() + enclMethod.getParameters().size();
            String varIdent = enclClassNameString() + "_" + node.getVariable().toString().replace("this.", "");
            if (atypeFactory.getChecker().getParentChecker().resultsForVar1.containsKey(varIdent)) {
                saveConstructorAssignments(varIdent, (JCTree.JCAssign) node);
            }
        } else {
            constructorIdent = null;
        }


        PropertyChecker checker = getLatticeSubchecker().getParentChecker();
        String var = enclClassNameString() + enclMethodNameString() + "_" + node.getVariable().toString();
        ArrayList<String> usedVars = new ArrayList<String>();
        ArrayList<String> relativeValues = new ArrayList<String>();
        JCTree.JCAssign varAssign = (JCTree.JCAssign) node;
        SMTStringPrinter printer = new SMTStringPrinter(enclClassNameString(), enclMethodNameString(), this.methodName, this.checkingMethodArgs, checker);
        if (node.getExpression() != null && node.getExpression().getClass().equals(JCTree.JCFieldAccess.class)) {
            if (enclMethodNameString().equals("<init>")) {
                fieldName = enclClassNameString() + "_" + node.getExpression().toString();
            } else {
                fieldName = enclClassNameString() + enclMethodNameString() + "_" + node.getExpression().toString();
            }
            relativeValues.add("(assert (= " + var + " " + fieldName + "))");
            if (checker.objectFields.containsKey(fieldName)) {
                usedVars.add(fieldName);
                addFieldInfoToContext(fieldName, relativeValues, usedVars);
            }
        } else

        if (node.getExpression() instanceof MethodInvocationTree) {
            varMethodInvocation = var;
            return;
        }
        else {
            relativeValues.add(printer.printVarAssign(varAssign));
        }
        checkExpression((JCTree.JCExpression) node.getExpression(), relativeValues, usedVars);
        if (checker.typeAnnos.containsKey(var) && !checker.typeAnnos.get(var).isEmpty()) {
            relativeValues.addAll(checker.typeAnnos.get(var));
            for (String typeWithVarName : checker.typeAnnos.get(var)) {
                ArrayList<String> passedAnnoArgs = new ArrayList<String>();
                getPassedArgs(typeWithVarName, passedAnnoArgs);
                if (!passedAnnoArgs.isEmpty()) {
                    for (String a : passedAnnoArgs) {
                        parseExprArg1(a, relativeValues, usedVars);
                    }
                }
            }
        }
        checker.resultsForVar1.put(var, relativeValues);
        checker.usedVarForVar1.put(var, usedVars);
    }

    private void addMethodInvToContext (MethodInvocationTree node) {
        ArrayList<String> relativeValues = new ArrayList<String>();
        ArrayList<String> usedVars = new ArrayList<String>();
        ArrayList<String> passedAnnoArgs = new ArrayList<String>();
        JCTree.JCMethodInvocation tree = (JCTree.JCMethodInvocation) node;

        if (this.varName != null && !this.varName.equals("")) {
            String var = enclClassNameString() + enclMethodNameString() + "_" + this.varName;
            //////////////////
            var = this.varName;
            /////////////////
            if (!tree.type.getAnnotationMirrors().isEmpty()) {
                for (AnnotationMirror am : tree.type.getAnnotationMirrors()) {
                    String tempVarType = getAnnotationFromType(am.toString(), this.varName) + "TEMP";
                    usedVars.add(varName + "TEMP");
                    relativeValues.add("(assert (= " + this.varName + " " + this.varName + "TEMP" + "))");
                    relativeValues.add(tempVarType);
                    getPassedArgs(tempVarType, passedAnnoArgs);
                    if (!passedAnnoArgs.isEmpty()) {
                        for (String a : passedAnnoArgs) {
                            String [] ar = a.split(" ");
                            for (String s : ar) {
                                if (!isNumeric(s) && !isOperand(s)) {
                                    String s1 = enclClassNameString() + tree.meth.toString() + "_" + s;
                                    if (!atypeFactory.getChecker().getParentChecker().resultsForVar1.containsKey(s1)) {
                                        s1 = enclClassNameString() + "_" + s;
                                    }
                                    if (tree.meth.toString().contains(".")) {
                                        //System.out.println("YAY " + tree.meth);
                                        //s1 = methodName + "_" + s;
                                        //if (!atypeFactory.getChecker().getParentChecker().resultsForVar1.containsKey(s1)) {
                                            String obj = enclClassNameString() + enclMethodNameString() + "_" + tree.meth.toString().substring(0, tree.meth.toString().indexOf("."));
                                        //    String clName = "";
                                        //    if (atypeFactory.getChecker().getParentChecker().initializedObjects.containsKey(obj)) {
                                        //        clName = atypeFactory.getChecker().getParentChecker().initializedObjects.get(obj);
                                        //    }
                                        //    s1 = clName + "_" + s;
                                        //    System.out.println("PPPPPPPPPPPPPPPPPPPP" + s1);

                                        //}
                                        for (Map.Entry<String, ArrayList<String>> entry : atypeFactory.getChecker().getParentChecker().objectFields.entrySet()) {
                                            String key = entry.getKey();
                                            if (key.contains(obj) && key.contains(s)) {
                                                //System.out.println("YAY " + atypeFactory.getChecker().getParentChecker().objectFields.get(key));
                                                if (!usedVars.contains(key)) {
                                                    usedVars.add(key);
                                                }
                                                for (String res : atypeFactory.getChecker().getParentChecker().objectFields.get(key)) {
                                                    if (!relativeValues.contains(res)) {
                                                        relativeValues.add(res);
                                                    }
                                                }
                                            }
                                        }

                                    }

                                    addInfoToContext(s1, relativeValues, usedVars);
                                }
                            }
                        }
                    }
                }
            }
            atypeFactory.getChecker().getParentChecker().resultsForVar1.put(var, relativeValues);
            atypeFactory.getChecker().getParentChecker().usedVarForVar1.put(var, usedVars);
        }
    }

    private String getNameToLookUp () {
        String nameToLookup = "";
        if (this.checkingMethodArgs) {
            nameToLookup = enclClassNameString() + this.methodName + "_" + varName;
            nameToLookup = enclClassNameString() + this.methodName + "_" + varName.substring(varName.indexOf("_") + 1);
        } else {
            if (enclMethod != null && !enclMethodNameString().equals("<init>")) {
                nameToLookup = enclClassNameString() + enclMethodNameString() + "_" + varName;
                nameToLookup = enclClassNameString() + enclMethodNameString() + "_" + varName.substring(varName.indexOf("_") + 1);
            } else {
                nameToLookup = enclClassNameString() + "_" + varName;
                nameToLookup = enclClassNameString() + "_" + varName.substring(varName.indexOf("_") + 1);
            }
        }
        return nameToLookup;
    }

    private void addInfoToLocalContext (String name, HashMap<String, ArrayList<String>> global, ArrayList<String> local) {
        if (global.containsKey(name)) {
            for (String res : global.get(name)) {
                if (!local.contains(res)) {
                    local.add(res);
                }
            }
        }
    }

    private void addFieldInfoToContext (String field, ArrayList<String> knowledge, ArrayList<String> vars) {
        addInfoToLocalContext(field, atypeFactory.getChecker().getParentChecker().objectFields, knowledge);
        addInfoToLocalContext(field, atypeFactory.getChecker().getParentChecker().objectFieldsVars, vars);
    }

    private void addInfoToGlobalContext (HashMap<String, ArrayList<String>> global, ArrayList<String> local, String var) {
        System.out.println("I'm in addInfoToGlobalContext method");
        if (global.containsKey(var)) {
            for (String res : local) {
                if (!global.get(var).contains(res)) {
                    global.get(var).add(res);
                }
            }
        } else {
            global.put(var, local);
        }
    }

    public static class Result {

        private LatticeSubchecker checker;

        private Set<AssignmentTree> malTypedAssignments = new HashSet<>();
        private Set<VariableTree> malTypedVars = new HashSet<>();
        private Set<ReturnTree> malTypedReturns = new HashSet<>();
        private Set<MethodTree> malTypedConstructors = new HashSet<>();

        private Map<MethodTree, List<Pair<AnnotatedDeclaredType, AnnotatedExecutableType>>> overriddenMethods = new HashMap<>();

        private Map<String, List<Invariant>> instanceInvariants = new HashMap<>();
        private Map<String, List<Invariant>> staticInvariants = new HashMap<>();

        private Map<String, List<Union<StatementTree, VariableTree, BlockTree>>> instanceInitializers = new HashMap<>();
        private Map<String, List<Union<StatementTree, VariableTree, BlockTree>>> staticInitializers = new HashMap<>();

        private Map<MethodInvocationTree, Set<Integer>> malTypedMethodParams = new HashMap<>();
        private Set<MethodInvocationTree> malTypedMethodReceivers = new HashSet<>();
        private Map<NewClassTree, Set<Integer>> malTypedConstructorParams = new HashMap<>();

        private Result(LatticeSubchecker checker) {
            this.checker = checker;
        }

        public LatticeSubchecker getChecker() {
            return checker;
        }

        public LatticeAnnotatedTypeFactory getTypeFactory() {
            return checker.getTypeFactory();
        }

        public Lattice getLattice() {
            return getTypeFactory().getLattice();
        }

        public boolean isWellTyped(AssignmentTree tree) {
            return !malTypedAssignments.contains(tree);
        }

        public boolean isWellTyped(VariableTree tree) {
            return !malTypedVars.contains(tree);
        }

        public boolean isWellTypedConstructor(MethodTree tree) {
            if (!isConstructor(tree)) {
                throw new IllegalArgumentException();
            }

            return !malTypedConstructors.contains(tree);
        }

        public boolean isWellTyped(ReturnTree tree) {
            return !malTypedReturns.contains(tree);
        }

        private void addInstanceInvariant(String className, Invariant invariant) {
            CollectionUtils.addToListMap(instanceInvariants, className, invariant);
        }

        private void addStaticInvariant(String className, Invariant invariant) {
            CollectionUtils.addToListMap(staticInvariants, className, invariant);
        }

        private void addInstanceInitializer(String className, Union<StatementTree, VariableTree, BlockTree> init) {
            CollectionUtils.addToListMap(instanceInitializers, className, init);
        }

        private void addStaticInitializer(String className, Union<StatementTree, VariableTree, BlockTree> init) {
            CollectionUtils.addToListMap(staticInitializers, className, init);
        }

        private void addMalTypedMethodParam(MethodInvocationTree tree, int param) {
            CollectionUtils.addToSetMap(malTypedMethodParams, tree, param);
        }

        private void addMalTypedConstructorParam(NewClassTree tree, int param) {
            CollectionUtils.addToSetMap(malTypedConstructorParams, tree, param);
        }

        public List<Pair<AnnotatedDeclaredType, AnnotatedExecutableType>> getOverriddenMethods(MethodTree tree) {
            return CollectionUtils.getUnmodifiableList(overriddenMethods, tree);
        }

        public List<Invariant> getInstanceInvariants(String className) {
            return CollectionUtils.getUnmodifiableList(instanceInvariants, className);
        }

        public List<Invariant> getStaticInvariants(String className) {
            return CollectionUtils.getUnmodifiableList(staticInvariants, className);
        }

        public List<Union<StatementTree, VariableTree, BlockTree>> getInstanceInitializers(String className) {
            return CollectionUtils.getUnmodifiableList(instanceInitializers, className);
        }

        public List<Union<StatementTree, VariableTree, BlockTree>> getStaticInitializers(String className) {
            return CollectionUtils.getUnmodifiableList(staticInitializers, className);
        }

        public Set<Integer> getMalTypedMethodParams(MethodInvocationTree tree) {
            return CollectionUtils.getUnmodifiableSet(malTypedMethodParams, tree);
        }

        public Set<MethodInvocationTree> getMalTypedMethodReceivers() {
            return Collections.unmodifiableSet(malTypedMethodReceivers);
        }

        public Set<Integer> getMalTypedConstructorParams(NewClassTree tree) {
            return CollectionUtils.getUnmodifiableSet(malTypedConstructorParams, tree);
        }

        public void addAll(Result result) {
            malTypedAssignments.addAll(result.malTypedAssignments);
            malTypedVars.addAll(result.malTypedVars);
            malTypedReturns.addAll(result.malTypedReturns);
            malTypedConstructors.addAll(result.malTypedConstructors);

            overriddenMethods.putAll(result.overriddenMethods);
            instanceInvariants.putAll(result.instanceInvariants);
            staticInvariants.putAll(result.staticInvariants);
            instanceInitializers.putAll(result.instanceInitializers);
            staticInitializers.putAll(result.staticInitializers);

            malTypedMethodParams.putAll(result.malTypedMethodParams);
            malTypedMethodReceivers.addAll(result.malTypedMethodReceivers);

            malTypedConstructorParams.putAll(result.malTypedConstructorParams);
        }
    }

    public static class Invariant {

        private String fieldName;
        private AnnotatedTypeMirror type;

        private Invariant(String fieldName, AnnotatedTypeMirror type) {
            this.fieldName = fieldName;
            this.type = type;
        }

        public String getFieldName() {
            return fieldName;
        }

        public AnnotatedTypeMirror getType() {
            return type;
        }
    }
}
