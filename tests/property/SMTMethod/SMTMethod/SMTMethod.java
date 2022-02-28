import java.util.*;
import edu.kit.iti.checker.property.subchecker.lattice.qual.*;

public class SMTMethod {

	public int z = 10;
	public int a = 10;
	public int t = 1;
	public int maximum = 1000;
	
	public SMTMethod() {
	
	}
	
	public @Interval(min = "1 * t", max = "m + 1") int dummy3(@Interval(min = "0", max = "a") int m, int second) {
	if (z < maximum) {
		@Interval(min = "1 * t", max = "z + 1") int nj = m + 1;
		int m5 = nj;
		return m5;
	}
		int m3 = 1;
		@Interval(min = "0", max = "maximum") int b = m + a;
		int m4 = b - 1;
		return m4;
	}

	public @Interval(min = "1", max = "z + 1") int calculateInv() {
		int inv = 4;
		if (5 > a) {
		inv = 5;
		inv = 4 + 1;
		inv = a * t;
		return inv;
		} else {
		@Interval(min = "0", max = "maximum") int forInv = dummy3(5, 2);
		inv = forInv;
		}
		inv = dummy3(z, 4);
		return inv;
	}
	
	public @Interval(min = "0", max = "z + 1") int addOne(@Interval(min = "0", max = "a") int m) {
	@Interval(min = "0", max = "a + 1") int added = m + 1;
	return added;
	}
	
	public @Interval(min = "1", max = "z + 1") int addOneMore(@Interval(min = "0", max = "10") int m) {
	@Interval(min = "0", max = "a + 1") int addedMore = m + 1;
	return addedMore;
	}
	
	public @Interval(min = "0", max = "z") int testMethodInv() {
		@Interval(min = "0", max = "z + 1") int testVar = addOneMore(10);
		@Interval(min = "0", max = "z + 1") int anotherVar = addOne(10);
		int returnVar = testVar - 1;
		return returnVar; 
	}
}

