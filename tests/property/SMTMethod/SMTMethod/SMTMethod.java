import java.util.*;
import edu.kit.iti.checker.property.subchecker.lattice.qual.*;

public class SMTMethod {

	public int z = 10;
	public int a = 10;
	public int t = 1;
	int maximum = 1000;
	
	public @Interval(min = "1 * t", max = "m + 1") int dummy3(@Interval(min = "0", max = "a") int m, int second) {
		int m3 = 1;
		@Interval(min = "0", max = "maximum") int b = m + a;
		int m4 = b - 1;
		return m4;
	}

	public @Interval(min = "0", max = "z") int calculateInv() {
		int inv = 4;
		inv = 5;
		inv = 4 + 1;
		inv = a * t;
		@Interval(min = "0", max = "maximum") int forInv = dummy3(5, 5);
		inv = forInv;
		return inv;
	}
	
}

