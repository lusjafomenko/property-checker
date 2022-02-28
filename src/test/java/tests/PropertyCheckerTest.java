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
package tests;

import edu.kit.iti.checker.property.checker.PropertyChecker;
import org.apache.commons.lang3.ObjectUtils;
import org.checkerframework.framework.test.CheckerFrameworkPerDirectoryTest;

import java.io.File;
import java.util.List;

@SuppressWarnings("nls")
public abstract class PropertyCheckerTest extends CheckerFrameworkPerDirectoryTest {

    public PropertyCheckerTest(List<File> testFiles, String latticeFile, String classesDir) {
        this(testFiles, latticeFile, classesDir, "edu.kit.iti.checker.property.subchecker.lattice.qual");
    }

    public PropertyCheckerTest(List<File> testFiles, String latticeFile, String classesDir, String qualPackage) {
        super(
                testFiles,
                PropertyChecker.class,
                "property",
                "-Anomsgtext",
                "-Astubs=stubs/",
                "-nowarn",
                "-Aflowdotdir=../flowdot",
                "-APropertyChecker_inDir=" + classesDir,
                "-APropertyChecker_outDir=" + "../property-checker-out",
                "-APropertyChecker_lattices=" + latticeFile,
                "-APropertyChecker_qualPkg=" + qualPackage,
                "-APropertyChecker_jmlDialect=" + ObjectUtils.defaultIfNull(System.getProperty("jmlDialect"), "key"),
                "-APropertyChecker_translationOnly=" + ObjectUtils.defaultIfNull(System.getProperty("translationOnly"), "false")
                );
    }
}
