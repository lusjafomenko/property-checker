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
import edu.kit.iti.checker.property.printer.SMTPrinter;
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
        //System.out.println("!!!!!!!!visiting return");
        //System.out.println(node.getExpression());
        this.varName = node.getExpression().toString();
        call(() -> super.visitReturn(node, p), () -> result.malTypedReturns.add(node));
        return null;
    }

    @Override
    public Void visitAssignment(AssignmentTree node, Void p) {
        call(() -> super.visitAssignment(node, p), () -> result.malTypedAssignments.add(node));
        return null;
    }

    @Override
    public Void visitVariable(VariableTree node, Void p) {
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

    @Override
    public Void visitMethod(MethodTree node, Void p) {
        MethodTree prevEnclMethod = enclMethod;
        enclMethod = node;
        System.out.println("!!!!!!!!!!!!!!visiting method " + node.getName());

    //    System.out.println("visiting method : " + enclMethod.toString());
    //    System.out.println(enclMethod.getModifiers().getAnnotations());
    //    if (!enclMethod.getModifiers().getAnnotations().isEmpty()) {
    //        for (AnnotationTree annoTree : enclMethod.getModifiers().getAnnotations()) {
    //            System.out.println(annoTree.getAnnotationType());
    //        }
    //        if (!enclMethod.getBody().getStatements().isEmpty()) {
    //            for (StatementTree sTree : enclMethod.getBody().getStatements()) {
    //                System.out.println("Statement:: " + sTree);
    //                if (sTree.toString().contains("return")) {
    //                    System.out.println("return statement:: " + sTree.toString().replace("return ", ""));
    //                    this.varName = sTree.toString().replace("return ", "");
    //                }
    //            }
    //        }
    //    }
        String key = enclClass.getSimpleName().toString() + "." + enclMethod.getName().toString();
        if (getLatticeSubchecker().getParentChecker().invokedMethods.containsKey(key)
                && getLatticeSubchecker().getParentChecker().invokedMethods.get(key).isEmpty()) {
        //    System.out.println("!!!!!!!visiting one of the invoked methods");

            if (!enclMethod.getModifiers().getAnnotations().isEmpty()) {
                for (AnnotationTree annoTree : enclMethod.getModifiers().getAnnotations()) {
                    getLatticeSubchecker().getParentChecker().invokedMethods.get(key).add(annoTree.toString());
                }
            }
            if (!enclMethod.getParameters().isEmpty()) {
                for (VariableTree methodParameter : enclMethod.getParameters()) {
                    getLatticeSubchecker().getParentChecker().invokedMethods.get(key).add(methodParameter.toString());
                }
            }
        //    System.out.println(getLatticeSubchecker().getParentChecker().invokedMethods);
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

    @Override
    public Void visitBlock(BlockTree node, Void p) {
        boolean prevEnclStaticInitBlock = enclStaticInitBlock;
        boolean prevEnclInstanceInitBlock = enclInstanceInitBlock;

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

    @Override
    protected void checkArguments(
            List<? extends AnnotatedTypeMirror> requiredArgs,
            List<? extends ExpressionTree> passedArgs,
            CharSequence executableName,
            List<?> paramNames) {

    //    System.out.println("required arguments of the " + executableName + " are " + requiredArgs);
    //    System.out.println("passed arguments are " + passedArgs);
    //    System.out.println("parameter names are " + paramNames);
        Pair<Tree, AnnotatedTypeMirror> preAssCtxt = visitorState.getAssignmentContext();
        try {
            for (int i = 0; i < requiredArgs.size(); ++i) {
                this.checkingMethodArgs = true;
                visitorState.setAssignmentContext(Pair.of((Tree) null, (AnnotatedTypeMirror) requiredArgs.get(i)));

                final int idx = i;
                this.varName = paramNames.get(i).toString();
    //            System.out.println("=======now is the var name: " + this.varName);
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
                this.checkingMethodArgs = false;
            }
        } finally {
            visitorState.setAssignmentContext(preAssCtxt);
        }
    }

    @Override
    protected void commonAssignmentCheck(Tree varTree, ExpressionTree valueExp, @CompilerMessageKey String errorKey, Object... extraArgs) {
        //System.out.println("varTree:: " + varTree.toString());
        //System.out.println("value esxpression::" + valueExp.toString());
        //System.out.println("value esxpression type::" + valueExp.getKind());
        if (varTree.getKind().name().equals("VARIABLE")) {
            JCTree.JCVariableDecl var = (JCTree.JCVariableDecl) varTree;
            this.varName = var.getName().toString();
        //    System.out.println(varName + " " + varTree.getKind().name());
            //System.out.println("from cas:  " + ((JCTree.JCVariableDecl) varTree).init.getStartPosition());
        } else if (varTree.getKind().name().equals("IDENTIFIER")){
            JCTree.JCIdent var = (JCTree.JCIdent) varTree;
            this.varName = var.getName().toString();
        //    System.out.println(varName + " " + varTree.getKind().name());
            //System.out.println("???????" + varTree.getKind().name());
            //this.varName = null;
        } else {
        //    System.out.println(varTree + " " + varTree.getKind().name());
        }
        if (valueExp.getKind().name().equals("METHOD_INVOCATION")) {
        //    System.out.println("§§§§§§" + varTree.getKind().name());
            this.isMethodInvocation = true;
        } else {
            this.isMethodInvocation = false;
        }
        super.commonAssignmentCheck(varTree, valueExp, errorKey, extraArgs);
    }

    @Override
    protected void commonAssignmentCheck(
            AnnotatedTypeMirror varType,
            AnnotatedTypeMirror valueType,
            Tree valueTree,
            @CompilerMessageKey String errorKey,
            Object... extraArgs) {
        commonAssignmentCheckStartDiagnostic(varType, valueType, valueTree);

        AnnotatedTypeMirror widenedValueType = atypeFactory.getWidenedType(valueType, varType);
        PropertyAnnotation pa = getLatticeSubchecker().getTypeFactory().getLattice().getPropertyAnnotation(varType);
    //    System.out.println("for the variable " + varName + " there is a property annotation " + pa + " and the varType is " + varType);
    //    System.out.println("the value tree is " + valueTree);
        PropertyChecker checker = getLatticeSubchecker().getParentChecker();
        boolean success = atypeFactory.getTypeHierarchy().isSubtype(widenedValueType, varType);

        if (!success && valueTree instanceof LiteralTree) {
            LiteralTree literal = (LiteralTree) valueTree;
            EvaluatedPropertyAnnotation epa = getLatticeSubchecker().getTypeFactory().getLattice().getEvaluatedPropertyAnnotation(varType);

            if (epa != null) {
                PropertyAnnotationType pat = epa.getAnnotationType();
                Class<?> literalClass = ClassUtils.literalKindToClass(literal.getKind());
                if (literalClass != null && literalClass.equals(pat.getSubjectType())) {
                    success = epa.checkProperty(literal.getValue());
                } else if (literal.getKind() == Kind.NULL_LITERAL && !pat.getSubjectType().isPrimitive()) {
                    success = epa.checkProperty(null);
                }

            } else if (!isMethodInvocation) {
                if (!pa.getActualParameters().isEmpty()) {
                    for (String p : pa.getActualParameters()) {
                        parseExprArg(p, checker.resultsForVar.get(varName), checker.usedVarForVar.get(varName));
                    }
                }
                // create .smt file, write SMT-conditions and check with z3;
                String smtName = getSMTFileName(varName);
                File file = createSMTFile(smtName);
                printSMT(checker, file, pa);
        //        System.out.println("!!!!!!!!!checking not method invocation and literal " + varName);
                success = checkWithZ3(smtName);
            }
        } else if (!success && isMethodInvocation) {

            if (this.checkingMethodArgs) {
                checker.resultsForVar.put(varName, new ArrayList<>());
                checker.usedVarForVar.put(varName, new ArrayList<>());
                if (!pa.getActualParameters().isEmpty()) {
                    for (String p : pa.getActualParameters()) {
                        parseExprArg(p, checker.resultsForVar.get(varName), checker.usedVarForVar.get(varName));
                    }
                }
                // create .smt file for the class
                String smtName = getSMTFileName(varName);
                File file = createSMTFile(smtName);
                printSMT(checker, file, pa);
                //this.isMethodInvocation = false;
        //        System.out.println("!!!!!!!!!checking method invocation and arguments " + varName);
                success = checkWithZ3(smtName);
                checker.resultsForVar.remove(varName);
                checker.usedVarForVar.remove(varName);
            } else {

            if (!pa.getActualParameters().isEmpty()) {
                for (String p : pa.getActualParameters()) {
                    parseExprArg(p, checker.resultsForVar.get(varName), checker.usedVarForVar.get(varName));
                }
            }
            // create .smt file for the class
            String smtName = getSMTFileName(varName);
            File file = createSMTFile(smtName);
            printSMT(checker, file, pa);
            //this.isMethodInvocation = false;
        //        System.out.println("!!!!!!!!!checking method invocation and literal " + varName);
            success = checkWithZ3(smtName);
            }
            //this.isMethodInvocation = false;
        } else if (!success && !isMethodInvocation) {
            if (enclMethod != null && checker.methodReturnVars.containsKey(enclMethod.getName().toString())) {
                System.out.println("annotations of enclosing method :: " + enclMethod.getModifiers().getAnnotations());
            }

            if (!pa.getActualParameters().isEmpty()) {
                for (String p : pa.getActualParameters()) {
                    parseExprArg(p, checker.resultsForVar.get(varName), checker.usedVarForVar.get(varName));
                }
            }
            String smtName = getSMTFileName(varName);
            File file = createSMTFile(smtName);
            printSMT(checker, file, pa);
        //    System.out.println("!!!!!!!!!checking not method invocation and not literal " + varName);
            success = checkWithZ3(smtName);

        }
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
        QualifierHierarchy qualifierHierarchy = atypeFactory.getQualifierHierarchy();
        Set<AnnotationMirror> constructorAnnotations =
                constructorType.getReturnType().getAnnotations();
        AnnotationMirror top = atypeFactory.getTop();

        AnnotationMirror constructorAnno =
                qualifierHierarchy.findAnnotationInHierarchy(constructorAnnotations, top);
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

    private void printMethodToSMT (PropertyAnnotation pa, String smtName, String methodName) {
        PropertyChecker checker = getLatticeSubchecker().getParentChecker();
        File file = Paths.get(getLatticeSubchecker().getParentChecker().getOutputDir(), smtName).toFile();
        file.getParentFile().mkdirs();
        FileUtils.createFile(file);

        try (BufferedWriter outS = new BufferedWriter(new FileWriter(file))) {
            SMTPrinter printerS = new SMTPrinter(outS, true, pa, checker, methodName);
            printerS.printUnit((JCTree.JCCompilationUnit) getCurrentPath().getCompilationUnit(), null);
        } catch (IOException e) {
            e.printStackTrace();
            System.exit(1);
        }
    }

    private void printSMT (PropertyChecker checker, File file, PropertyAnnotation pa) {
        if (checker.resultsForVar.containsKey(varName)) {
            try (BufferedWriter outS = new BufferedWriter(new FileWriter(file))) {
                SMTFilePrinter printer = new SMTFilePrinter(outS, checker, varName);
                if (checker.usedVarForVar.containsKey(varName)) {
                    ArrayList<String> varDecs = checker.usedVarForVar.get(varName);
                    for (String v : varDecs) {
                        printer.print("(declare-const " + v + " Int)");
                        printer.println();
                    }
                }
                printer.print("(declare-const " + varName + " Int)");
                printer.println();
                ArrayList<String> results = checker.resultsForVar.get(varName);
                for (String r : results) {
                    printer.printLine(r);
                }
                if (enclMethod != null) {
                    printer.printAnnoToProve(pa, varName);
                }
                printer.print("(check-sat)");

            } catch (IOException e) {
                e.printStackTrace();
            }
        }
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
            System.out.println(varName);
            System.out.println(smtName);
            System.out.println("[Stdout] " + line);
            if (line.equals("unsat")) success = true;
            brCleanUp.close();
//                                runtime.exit(0);
        } catch (IOException e) {
            e.printStackTrace();
        }
        return success;
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

    int count = 0;
    private String getSMTFileName (String varName) {
        //int count = 0;
        String smtName = getEnclClassName().toString() + varName + "_" + count + ".smt";
        if (enclMethod != null) {
            smtName = getEnclClassName().toString() + getEnclMethodNameName().toString() + varName + "_" + count + ".smt";
        }
        count++;
        return smtName;
    }

    private File createSMTFile (String smtName) {
        File file = Paths.get(getLatticeSubchecker().getParentChecker().getOutputDir(), smtName).toFile();
        file.getParentFile().mkdirs();
        FileUtils.createFile(file);
        return file;
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
