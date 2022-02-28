package smt_test;
import java.util.*;
import edu.kit.iti.checker.property.subchecker.lattice.qual.*;


public class SMTtestLess {
	
	@Less(value="10") int v = 5;
	int ttt = 10;
	
	
	public void testMethod() {
		SMTtestMethod m = new SMTtestMethod();
		//int twenty = m.age;
		@Interval(min = "0", max = "ttt") int ten = m.x;
	}
}
