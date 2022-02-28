import java.util.*;
import edu.kit.iti.checker.property.subchecker.lattice.qual.*;

public class SMTClassVar {

	int a = 10;
	int thousend = 1000;
	
	public @Interval(min = "0", max = "a") int b = 5;
	@Interval(min = "0", max = "a") int c = b;
	@Interval(min = "0", max = "a") int d = b + c;
	
	@Interval(min = "0", max = "d") int e = a / 2;
	@Interval(min = "0", max = "1000") int f = ((a + b) % d - 1) * 100;
	@Interval(min = "0", max = "thousend") int g = ((a + c) % d - 1) * 100;
	
	@Less(value = "1000") int l0 = 10;
	@Less(value = "thousend") int l1 = 10;
	@Less(value = "thousend") int l2 = a;
	@Less(value = "thousend") int l3 = d + a * b;
	@Less(value = "f") int l4 = d * a;
	
	// :: error: assignment.type.incompatible
	@Interval(min = "0", max = "a") int err = thousend;
	
	@Interval(min = "0", max = "a") int one = 1;
}
