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
package edu.kit.iti.checker.property.checker;

import com.sun.source.util.TreePath;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import edu.kit.iti.checker.property.config.Config;
import edu.kit.iti.checker.property.printer.JavaJMLPrinter;
import edu.kit.iti.checker.property.printer.PrettyPrinter;
import edu.kit.iti.checker.property.subchecker.lattice.LatticeVisitor.Result;
import edu.kit.iti.checker.property.util.FileUtils;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.common.basetype.BaseTypeVisitor;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Paths;
import java.util.List;

public class PropertyVisitor extends BaseTypeVisitor<PropertyAnnotatedTypeFactory> {

    protected PropertyVisitor(BaseTypeChecker checker, PropertyAnnotatedTypeFactory typeFactory) {
        super(checker, typeFactory);
    }

    public PropertyVisitor(BaseTypeChecker checker) {
        this(checker, null);
    }

    @SuppressWarnings("nls")
	@Override
    public void visit(TreePath path) {
        super.visit(path);

        File file = Paths.get(getPropertyChecker().getOutputDir(), getRelativeSourceFileName()).toFile();
//        File fileS = Paths.get(getPropertyChecker().getOutputDir(), "test.smt").toFile();
        file.getParentFile().mkdirs();
//        fileS.getParentFile().mkdirs();
        FileUtils.createFile(file);
//        FileUtils.createFile(fileS);

        //test usage of SMTPrinter. Must not be here!
        //try (BufferedWriter outS = new BufferedWriter(new FileWriter(fileS))) {
        //    SMTPrinter printerS = new SMTPrinter(outS, true);
        //    printerS.printUnit((JCCompilationUnit) path.getCompilationUnit(), null);
        //} catch (IOException e) {
        //    e.printStackTrace();
        //    System.exit(1);
        //}

        try (BufferedWriter out = new BufferedWriter(new FileWriter(file))) {
        	List<Result> results = getPropertyChecker().getResults(getAbsoluteSourceFileName());
        	if (results.isEmpty()) {
        		PrettyPrinter printer = new PrettyPrinter(out, true);
            	printer.printUnit((JCCompilationUnit) path.getCompilationUnit(), null);
        	} else {
        		JavaJMLPrinter printer = new JavaJMLPrinter(getPropertyChecker().getResults(getAbsoluteSourceFileName()), getPropertyChecker(), out);
            	printer.printUnit((JCCompilationUnit) path.getCompilationUnit(), null);
            	System.out.println(String.format(
            			"Wrote file %s with: \n\t%d assertions (to be proven in JML)\n\t%d assumptions (proven by checker)\n\t%d non-free method preconditions (to be proven in JML)\n\t%d free method preconditions (proven by checker)",
            			getRelativeSourceFileName(),
            			printer.getAssertions(), printer.getAssumptions(),
            			printer.getMethodCallPreconditions(), printer.getFreeMethodCallPreconditions()));
        	}
        } catch (IOException e) {
            e.printStackTrace();
            System.exit(1);
        }
    }

    protected String getAbsoluteSourceFileName() {
        return Paths.get(root.getSourceFile().getName()).toAbsolutePath().toString();
    }

    protected String getRelativeSourceFileName() {
        String classesDir = Paths.get(getPropertyChecker().getOption(Config.INPUT_DIR_OPTION)).toAbsolutePath().toString();
        return getAbsoluteSourceFileName().substring(classesDir.length());
    }

    public PropertyChecker getPropertyChecker() {
        return (PropertyChecker) checker;
    }
}
