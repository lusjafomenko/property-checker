package edu.kit.iti.checker.property.printer;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.List;
import edu.kit.iti.checker.property.checker.PropertyAnnotatedTypeFactory;
import edu.kit.iti.checker.property.checker.PropertyChecker;
import edu.kit.iti.checker.property.lattice.PropertyAnnotation;
import edu.kit.iti.checker.property.lattice.PropertyAnnotationType;

import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;


public class SMTPrinter extends PrettyPrinter {

    //all variables declared in the class;
    //used for testing the code; could be a map - and maybe used to simulate SSA
    private ArrayList<String> varDecs;
    //private String prop;
    //private String wfCond;
    private PropertyAnnotation pa;
    protected PropertyChecker checker;
    protected PropertyAnnotatedTypeFactory propertyFactory;

    public SMTPrinter(Writer out, boolean sourceOutput, PropertyAnnotation pa, PropertyChecker checker) {
        super(out, sourceOutput);
        this.varDecs = new ArrayList<String>();
        this.pa = pa;
        this.checker = checker;
        this.propertyFactory = checker.getPropertyFactory();
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
                            printBExpr((JCTree.JCBinary) tree.init);
                        } else {
                            printExpr(tree.init);
                        }
                        print("))");
                        println();
                    }
                    if (tree.mods.annotations != null) {
                        println();

                        for(JCTree.JCAnnotation anno : tree.mods.annotations) {
                            visitAnnotation(anno, tree.name.toString());
                            //    print(tree.mods.annotations);
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
        try {
            JCTree.JCModifiers mods = tree.mods;
            List<JCTree.JCAnnotation> modAnns = mods.annotations;
//            List<JCTree.JCStatement> statList = tree.getBody().getStatements();
//            System.out.println(statList.get(statList.size()));
            //print annotations as they are; TODO: translate annotations to SMTlib
            print(modAnns);


            if (modAnns != null) {
                    List<JCTree.JCVariableDecl> ps = tree.params;
                    for(JCTree.JCVariableDecl p : ps) {
//                        printExpr(p);
                        visitVarDef(p);
                        println();
                }
                    if(tree.body != null) {
                        printStat(tree.body);
                    }
            }

            println();
            if (tree.mods.annotations != null) {
                println();
                for(JCTree.JCAnnotation anno : tree.mods.annotations) {
                    visitAnnotation(anno, tree.name.toString());
                    //    print(tree.mods.annotations);
                }
            }
//            printTypeParameters(tree.typarams);
//            printExpr(tree.restype);
//            print(tree.getReturnType().toString());
//            print(tree.getReturnType());
    } catch (IOException e) {
            e.printStackTrace();
        }
    }

    public void visitAnnotation(JCTree.JCAnnotation tree, String name) {
        try {
            println();
            String repParam = replacePropertyParameters(this.pa, name);
            String repSub = repParam.replace("§subject§", name);
            String smtString = "(assert " + toSMT(parseStringAnno(repSub)) + ")";
            print(smtString);
        } catch (IOException e) {
            e.printStackTrace();
        }


    }

    @Override public void visitReturn(JCTree.JCReturn tree) {
// No pseudoassignements!
    }

    @Override
    public void visitImport(JCTree.JCImport tree) {

    }

    @Override
    public void visitClassDef(JCTree.JCClassDecl tree) {
        try {
            printBlock(tree.defs);
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
        //    System.out.println(pa.getName() + " " + pa.getAnnotationType().getProperty());
        //    System.out.println(pa.getAnnotationType().getWFCondition());
            for (int i = 0; i < parL.size(); i++) {
                String old = "§" + parL.get(i).getName() + "§";
                String act = acPar.get(i);
                prop = prop.replace(old, act);
            }
            prop = prop.replace("§subject§", name);
        }
        return prop;
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
            System.out.println(rSide);
        } else {
            rSide = parsedAnno.get(parsedAnno.size()-1);
//            System.out.println(rSide);
        }
        return "(" + op + " " + lSide + " " + rSide + ")";
    }


}
