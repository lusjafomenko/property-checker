package edu.kit.iti.checker.property.printer;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.List;
import edu.kit.iti.checker.property.lattice.EvaluatedPropertyAnnotation;
import edu.kit.iti.checker.property.lattice.PropertyAnnotation;
import edu.kit.iti.checker.property.subchecker.lattice.LatticeVisitor;
import org.checkerframework.common.basetype.BaseTypeChecker;

import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;


public class SMTPrinter extends PrettyPrinter {

    //all variables declared in the class;
    //used for testing the code; could be a map - and maybe used to simulate SSA
    private ArrayList<String> varDecs;

    public SMTPrinter(Writer out, boolean sourceOutput) {
        super(out, sourceOutput);
        this.varDecs = new ArrayList<String>();
    }

    //by variable definition: print variable declaration in SMTlib, print assertions if initialized
    @Override
    public void visitVarDef(JCTree.JCVariableDecl tree) {
        try {
            if (tree.vartype.toString().equals("int")){
                if (!varDecs.contains(tree.name.toString())) {
                    varDecs.add(tree.name.toString());
                    print("(declare-const " + tree.name + " Int)");
                    if (tree.mods.annotations != null) {
                        println();
                        print(tree.mods.annotations);
                    }
                }
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
            //print annotations as they are; TODO: translate annotations to SMTlib
            print(modAnns);
            println();
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
//            printTypeParameters(tree.typarams);
//            printExpr(tree.restype);
//            print(tree.getReturnType().toString());
//            print(tree.getReturnType());
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
        for (List<? extends JCTree> l = trees; l.nonEmpty(); l = l.tail) {
            printStat(l.head);
            println();
        }
    }

}
