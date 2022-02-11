import java.util.*;
import edu.kit.iti.checker.property.subchecker.lattice.qual.*;

public class SMTClassVarRep {

	int a = 1000;
	int thousend = 1000;
	@Interval(min = "0", max = "a") int err = thousend;
}
