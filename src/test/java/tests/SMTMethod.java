package tests;

import java.io.File;
import java.util.List;

import org.junit.runners.Parameterized.Parameters;

@SuppressWarnings("nls")
public class SMTMethod extends PropertyCheckerTest {
    public SMTMethod(List<File> testFiles) {
        super(
                testFiles,
                "tests/property/SMTMethod/lattice_interval" + 
                ",tests/property/SMTMethod/lattice_less",
                "tests/property/SMTMethod");
    }

    @Parameters
    public static String[] getTestDirs() {
        return new String[] {"property/SMTMethod"};
    }
}
