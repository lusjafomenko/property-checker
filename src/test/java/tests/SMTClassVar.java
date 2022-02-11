package tests;

import java.io.File;
import java.util.List;

import org.junit.runners.Parameterized.Parameters;

@SuppressWarnings("nls")
public class SMTClassVar extends PropertyCheckerTest {
    public SMTClassVar(List<File> testFiles) {
        super(
                testFiles,
                "tests/property/SMTClassVar/lattice_interval" + 
                ",tests/property/SMTClassVar/lattice_less",
                "tests/property/SMTClassVar");
    }

    @Parameters
    public static String[] getTestDirs() {
        return new String[] {"property/SMTClassVar"};
    }
}
