package edu.kit.iti.checker.property.printer;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeInfo;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;
import edu.kit.iti.checker.property.checker.PropertyAnnotatedTypeFactory;
import edu.kit.iti.checker.property.checker.PropertyChecker;
import edu.kit.iti.checker.property.lattice.PropertyAnnotation;
import edu.kit.iti.checker.property.lattice.PropertyAnnotationType;
import edu.kit.iti.checker.property.subchecker.lattice.LatticeAnnotatedTypeFactory;
import org.checkerframework.common.basetype.BaseTypeChecker;

import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import static com.sun.tools.javac.tree.JCTree.Tag.*;


public class SMTPrinter extends PrettyPrinter {

    //all variables declared in the class;
    //used for testing the code; could be a map - and maybe used to simulate SSA
    private ArrayList<String> varDecs;
    //private String prop;
    //private String wfCond;
    private PropertyAnnotation pa;
    protected PropertyChecker checker;
    protected PropertyAnnotatedTypeFactory propertyFactory;
    protected String methodName = null;
    Map <String, PropertyAnnotationType> annotationTypes = new HashMap<>();

    public SMTPrinter(Writer out, boolean sourceOutput, PropertyAnnotation pa, PropertyChecker checker) throws IOException {
        super(out, sourceOutput);
        this.varDecs = new ArrayList<String>();
        this.pa = pa;
        this.checker = checker;
        this.propertyFactory = checker.getPropertyFactory();
        System.out.println("invoked");
        print("(set-logic QF_UFLIA)");
        for (BaseTypeChecker typeChecker : this.checker.getSubcheckers()) {
            LatticeAnnotatedTypeFactory lf = (LatticeAnnotatedTypeFactory) typeChecker.getTypeFactory();
            this.annotationTypes.putAll(lf.getLattice().getAnnotationTypes());
        }
    }

    public SMTPrinter(Writer out, boolean sourceOutput, PropertyAnnotation pa, PropertyChecker checker, String methodName) throws IOException {
        super(out, sourceOutput);
        this.varDecs = new ArrayList<String>();
        this.pa = pa;
        this.checker = checker;
        this.propertyFactory = checker.getPropertyFactory();
        this.methodName = methodName;
        print("(set-logic QF_UFLIA)");
        for (BaseTypeChecker typeChecker : this.checker.getSubcheckers()) {
            LatticeAnnotatedTypeFactory lf = (LatticeAnnotatedTypeFactory) typeChecker.getTypeFactory();
            this.annotationTypes.putAll(lf.getLattice().getAnnotationTypes());
        }
    }

    //by variable definition: print variable declaration in SMTlib, print assertions if initialized
    @Override
    public void visitVarDef(JCTree.JCVariableDecl tree) {
        try {
            if (tree.vartype.toString().equals("int")){
                if (!varDecs.contains(tree.name.toString())) {
                    varDecs.add(tree.name.toString());
                    print("(declare-const " + tree.name + " Int)");

                    if (tree.init != null) {
                        println();
                        print("(assert (= " + tree.name + " ");
                        if (tree.init.getClass().equals(JCTree.JCBinary.class)) {
                            visitBinary((JCTree.JCBinary) tree.init);
                        } else {
                            printExpr(tree.init);
                        }
                        if (tree.init.getClass().equals(JCTree.JCMethodInvocation.class)) {
                            visitApply((JCTree.JCMethodInvocation) tree.init);
                        }
                        print("))");
                        println();
                    }

                    if (tree.mods.annotations != null) {
                        for(JCTree.JCAnnotation anno : tree.mods.annotations) {
                            ArrayList<String> parsedCond = new ArrayList<String>();
                            ArrayList<String> parsedParamNames = new ArrayList<String>();
                            ArrayList<String> parsedParam = new ArrayList<String>();
                            if (annotationTypes.containsKey(anno.annotationType.toString())) {
                                getPropertyFromAnntotation(annotationTypes.get(anno.annotationType.toString()).toString(), parsedCond);
                                getParameterNamesFromAnnotation(annotationTypes.get(anno.annotationType.toString()).toString(), parsedParamNames);
                            }
                            getParametersFromAnnotation(anno.toString(), parsedParam);
                            visitAnnotation(anno, tree.name.toString(), parsedCond, parsedParam, parsedParamNames);
                        }
                    }

                }

            }
        } catch (IOException e) {
            throw new SMTPrinter.UncheckedIOException(e);
        }
    }

//    public void printSMTExpr(JCTree.JCExpression tree) throws IOException {
//        if (tree != null) {
//            println();
//            print("(assert (= " + tree.);
//            if (tree.getClass().equals(JCTree.JCBinary.class)) {
//                printBExpr((JCTree.JCBinary) tree);
//            } else {
//                printExpr(tree);
//            }
//            print("))");
//            println();
//        }
//    }


    //by visiting a method with annotated return type: print annotation, print parameter declarations, print body
    @Override
    public void visitMethodDef(JCTree.JCMethodDecl tree) {
        if(methodName == null) {
           // try {
           //     print("(check-sat)");
           // } catch (IOException e) {
           //     e.printStackTrace();
           // }
            return;
        }
        if (methodName.equals(tree.getName().toString())) {
            try {
                JCTree.JCModifiers mods = tree.mods;
                List<JCTree.JCAnnotation> modAnns = mods.annotations;

                if (modAnns != null) {
                    List<JCTree.JCVariableDecl> ps = tree.params;
                    for(JCTree.JCVariableDecl p : ps) {
                        visitVarDef(p);
                        println();
                    }
                    if(tree.body != null) {
                        for (JCTree.JCStatement stat : tree.body.getStatements()) {
                            if (stat.getClass().equals(JCTree.JCVariableDecl.class)) {
                                visitVarDef((JCTree.JCVariableDecl) stat);
                            }
                            if (stat.getClass().equals(JCTree.JCReturn.class)) {
                                if (tree.mods.annotations != null) {
                                    println();
                                    for(JCTree.JCAnnotation anno : tree.mods.annotations) {
                                        visitReturn((JCTree.JCReturn) stat, anno);
                                        return;
                                    }
                                }
                            }
                        }
                    }

                println();

                }

            } catch (IOException e) {
                e.printStackTrace();
            }
        }

    }

    public void visitAnnotation(JCTree.JCAnnotation tree, String name, ArrayList<String> cond, ArrayList<String> params, ArrayList<String> paramNames) {
        try {
            println();
            ArrayList<String> repConds = new ArrayList<String>();
            for (String s : cond) {
                for (int i = 0; i < params.size();  i++) {
                    s = s.replaceAll("§" + paramNames.get(i) + "§", params.get(i));
                }
                String repSub = s.replaceAll("§subject§", name);
                repConds.add(repSub);
            }
            if(!(methodName == null) && !(methodName.equals("main"))) {
                String wfCond = "(assert (and " + toSMT(parseStringAnno(repConds.get(1))) + " " + toSMT(parseStringAnno(repConds.get(0))) + "))";
                print(wfCond);
                println();
                //String property = "(assert " + toSMT(parseStringAnno(repConds.get(0))) + ")";
                //print(property);
                //println();
            } else {
                String wfCond = "(assert (or (not " + toSMT(parseStringAnno(repConds.get(1))) + ") (not " + toSMT(parseStringAnno(repConds.get(0))) + ")))";
                print(wfCond);
                println();
                //String property = "(assert (not " + toSMT(parseStringAnno(repConds.get(0))) + "))";
                //print(property);
                //println();
            }

        } catch (IOException e) {
            e.printStackTrace();
        }

    }

    public void visitAnnotation(JCTree.JCAnnotation tree, String name) {
        try {
            println();
            String repParam = replacePropertyParameters(this.pa, name);
            String repSub = repParam.replace("§subject§", name);
            String repCond = replaceCondParameters(this.pa, name);
            String smtString = "(assert (not " + toSMT(parseStringAnno(repSub)) + "))";
            String smtCond = "(assert (not " + toSMT(parseStringAnno(repCond)) + "))";
            print(smtCond);
            println();
            print(smtString);
        } catch (IOException e) {
            e.printStackTrace();
        }


    }

    //public void visitIf(JCTree.JCIf tree) {
    //    try {
    //        println();
    //        print("(assert " + toSMT(parseStringAnno(tree.cond.toString().substring(1, tree.cond.toString().length() - 2))));
    //        //print(tree.cond.toString());
    //        //tree.cond.toString();
    //        println();
    //        //print(tree.thenpart.toString());
    //        JCTree.JCBlock block = (JCTree.JCBlock) tree.thenpart;
    //        //print(block.toString());
    //        //printBlock(block.getStatements());
    //        for (JCTree.JCStatement st : block.getStatements()) {
    //            if(st.getClass().equals(JCTree.))
    //        }
    //        println();
    //        //print(tree.elsepart.toString());
    //    } catch (IOException e) {
    //        e.printStackTrace();
    //    }
    //}

    public void visitReturn(JCTree.JCReturn tree, JCTree.JCAnnotation anno) {
// No pseudoassignements!
        visitAnnotation(anno, tree.getExpression().toString());
    }

    @Override
    public void visitImport(JCTree.JCImport tree) {

    }

    @Override
    public void visitClassDef(JCTree.JCClassDecl tree) {
        try {
            printBlock(tree.defs);
            System.out.println(methodName);
            print("(check-sat)");
        } catch (IOException e) {
            throw new PrettyPrinter.UncheckedIOException(e);
        }
    }

    @Override
    public void visitPackageDef(JCTree.JCPackageDecl tree) {
//ignore package definition, because not relevant for SMT
    }

    //print binary expression in SMTlib
    public void printBExpr(JCTree.JCBinary tree) throws IOException {
        print("(");
        printOperator(tree.getTag());
        print(" ");
        if(tree.lhs.getClass().equals(JCTree.JCBinary.class)) {
            printBExpr((JCTree.JCBinary) tree.lhs);
            print(" ");
        } else {
            printExpr(tree.lhs);
            print(" ");
        }

        if (tree.rhs.getClass().equals(JCTree.JCBinary.class)) {
            printBExpr((JCTree.JCBinary) tree.rhs);
        } else {
           printExpr(tree.rhs);
        }
        print(")");
    }

    public void visitBinary(JCTree.JCBinary tree) {
        try {
            int ownprec = TreeInfo.opPrec(tree.getTag());
            open(prec, ownprec);
            print("(");
            printOperator(tree.getTag());
            print(" ");
            printExpr(tree.lhs, ownprec);
            print(" ");
            printExpr(tree.rhs, ownprec + 1);
            print(")");
            close(prec, ownprec);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    public void visitParens(JCTree.JCParens tree) {
        try {
            printExpr(tree.expr);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    //supported operators
    public void printOperator(JCTree.Tag tag) throws IOException {
        switch(tag) {
            case MINUS: print("-");
                        break;
            case PLUS: print("+");
                        break;
            case ASSIGN: print("=");
                        break;
            case MUL: print("*");
                        break;
            case DIV: print("div");
                        break;

            default: print("");
                    break;
        }
    }

    /** Print a block.
     */
    @Override
    public void printBlock(List<? extends JCTree> stats) throws IOException {
        printStats(stats);
    }

    /** Derived visitor method: print list of statements, each on a separate line.
     */
    @Override
    public void printStats(List<? extends JCTree> trees) throws IOException {
        for (List<? extends JCTree> l = trees.tail; l.nonEmpty(); l = l.tail) {
                printStat(l.head);
                println();
        }
    }

    private String replacePropertyParameters(PropertyAnnotation pa, String name) {
        java.util.List<PropertyAnnotationType.Parameter> parL = pa.getAnnotationType().getParameters();
        java.util.List<String> acPar = pa.getActualParameters();
        String prop = "?";
        if (!parL.isEmpty()) {
            prop = pa.getAnnotationType().getProperty();
            for (int i = 0; i < parL.size(); i++) {
                String old = "§" + parL.get(i).getName() + "§";
                String act = acPar.get(i);
                prop = prop.replace(old, act);
            }
            prop = prop.replace("§subject§", name);
        }
        return prop;
    }

    private String replaceCondParameters(PropertyAnnotation pa, String name) {
        java.util.List<PropertyAnnotationType.Parameter> parL = pa.getAnnotationType().getParameters();
        java.util.List<String> acPar = pa.getActualParameters();
        String cond = "?";
        if (!parL.isEmpty()) {
            cond = pa.getAnnotationType().getWFCondition();
            //    System.out.println(pa.getName() + " " + pa.getAnnotationType().getProperty());
            //    System.out.println(pa.getAnnotationType().getWFCondition());
            for (int i = 0; i < parL.size(); i++) {
                String old = "§" + parL.get(i).getName() + "§";
                String act = acPar.get(i);
                cond = cond.replace(old, act);
            }
            cond = cond.replace("§subject§", name);
        }
        return cond;
    }

    private ArrayList<String> parseStringAnno (String anno) {
        ArrayList<String> listAnno = new ArrayList<String>();
        String[] s = anno.split(" ");
        for (String s1 : s) {
//            System.out.println(s1);
            listAnno.add(s1);
        }
        return listAnno;
    }

    private String toSMT(ArrayList<String> parsedAnno) {
        String smt = "";
        if (parsedAnno.size() == 1) {
            smt = parsedAnno.get(0);
        }
        if (parsedAnno.contains("&&")) {
            smt = parseAnd(parsedAnno, "&&");
//            smt = "(and (" + toSMT(leftSide) + " " + toSMT(rightSide) + ")";
        }
         else if (parsedAnno.contains(">=")) {
            smt = parseAnd(parsedAnno, ">=");
//            smt = "(>= (" + toSMT(leftSide) + " " + toSMT(rightSide) + ")";
        } else if (parsedAnno.contains("<=")) {
             smt = parseAnd(parsedAnno, "<=");
        } else if (parsedAnno.contains(">")) {
             smt = parseAnd(parsedAnno, ">");
        } else if (parsedAnno.contains("<")) {
             smt = parseAnd(parsedAnno, "<");
        } else if (parsedAnno.contains("+")) {
             smt = parseAnd(parsedAnno, "+");
        } else if (parsedAnno.contains("-")) {
             smt = parseAnd(parsedAnno, "-");
        } else if (parsedAnno.contains("*")) {
             smt = parseAnd(parsedAnno, "*");
        } else if (parsedAnno.contains("/")) {
             smt = parseAnd(parsedAnno, "/");
        } else if (parsedAnno.contains("%")) {
             smt = parseAnd(parsedAnno, "%");
        }
        return  smt;
    }

    private String parseAnd (ArrayList<String> parsedAnno, String op) {
        int index = parsedAnno.indexOf(op);
        ArrayList<String> leftSide = new ArrayList<String>();
        ArrayList<String> rightSide = new ArrayList<String>();
        String lSide;
        String rSide;
        if (index - 1 > 0) {
            for (String s : parsedAnno.subList(0, index )) {
                leftSide.add(s);
            }
            lSide = toSMT(leftSide);
        } else {
            lSide = parsedAnno.get(0);
        }
        if (index + 1 < parsedAnno.size() - 1) {
            for (String s : parsedAnno.subList(index + 1, parsedAnno.size())) {
                rightSide.add(s);
            }
            rSide = toSMT(rightSide);
//            System.out.println(rSide);
        } else {
            rSide = parsedAnno.get(parsedAnno.size()-1);
//            System.out.println(rSide);
        }
        if (op.equals("&&")) {
            op = "and";
        }
        if (op.equals("/")) {
            op = "div";
        }
        if (op.equals("%")) {
            op = "mod";
        }
        return "(" + op + " " + lSide + " " + rSide + ")";
    }

    private ArrayList<String> getParametersFromAnnotation (String anno, ArrayList<String> parameters) {
        if (anno.contains("\"")) {
            String s = anno.substring(anno.indexOf("\"") + 1);
            String rest = s.substring(s.indexOf("\"") + 1);
            s = s.substring(0, s.indexOf("\""));
            parameters.add(s);
            getParametersFromAnnotation(rest, parameters);
        }
        return parameters;
    }

    private ArrayList<String> getParameterNamesFromAnnotation (String anno, ArrayList<String> paramNames) {
        String paramString = anno.substring(anno.indexOf("(") + 1, anno.indexOf(")"));
        String [] s = paramString.split(", ");
        for (String s1 : s) {
            String [] temp = s1.split(" ");
            paramNames.add(temp[1]);
        }
        return paramNames;
    }

    private ArrayList<String> getPropertyFromAnntotation (String anno, ArrayList<String> properties) {
        ArrayList<String> listAnno = new ArrayList<String>();
        String[] s = anno.split(" ");
        for (String s1 : s) {
            listAnno.add(s1);
        }
        String property = "";
        String wfCond = "";
        if (listAnno.contains("<==>")) {
            int i = listAnno.indexOf("<==>") + 1;
            while (i < listAnno.size() && !listAnno.get(i).equals("for")) {
                property = property + listAnno.get(i) + " ";
                i++;
            }
            if (listAnno.get(i).equals("for")) {
                i++;
                while (i < listAnno.size()) {
                    wfCond = wfCond + listAnno.get(i) + " ";
                    i++;
                }
            }
        }
        properties.add(property);
        properties.add(wfCond);
        return properties;
    }

    public void checkVarDec(JCTree.JCCompilationUnit tree, JCTree.JCClassDecl cdef) throws IOException {
        docComments = tree.docComments;
        printDocComment(tree);

        boolean firstImport = true;
        for (List<JCTree> l = tree.defs;
             l.nonEmpty() &&
                     (cdef == null ||
                             l.head.hasTag(IMPORT) || l.head.hasTag(PACKAGEDEF));
             l = l.tail) {
            System.out.println(l.head.getTag().toString());
            if (l.head.hasTag(IMPORT)) {
                JCTree.JCImport imp = (JCTree.JCImport)l.head;
                Name name = TreeInfo.name(imp.qualid);
                if (name == name.table.names.asterisk ||
                        cdef == null) {
                    if (firstImport) {
                        firstImport = false;
                        println();
                    }
                    printStat(imp);
                }
            } else if (l.head.hasTag(CLASSDEF)) {
                printStat(l.head);
            //}else if (l.head.hasTag(METHODDEF)) {
             //   print("(check-sat)");
             //   return;
            } else {
                printStat(l.head);
            }
        }
        if (cdef != null) {
            printStat(cdef);
            println();
        }


    }



}
