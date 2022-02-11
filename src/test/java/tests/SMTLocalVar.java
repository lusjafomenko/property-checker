package tests;

import java.io.File;
import java.util.List;

import org.junit.runners.Parameterized.Parameters;

@SuppressWarnings("nls")
public class SMTLocalVar extends PropertyCheckerTest {
    public SMTLocalVar(List<File> testFiles) {
        super(
                testFiles,
                "tests/property/SMTLocalVar/lattice_interval" + 
                ",tests/property/SMTLocalVar/lattice_less",
                "tests/property/SMTLocalVar");
    }

    @Parameters
    public static String[] getTestDirs() {
        return new String[] {"property/SMTLocalVar"};
    }
}
