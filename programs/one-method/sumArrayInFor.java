public class main {

	public static void main(string[] args) {
		int n=4;
		int s,i;

		int[] v = new int[n + 1];
		for(i=0; i<v.length; ++i) {
			v[i] = i;
		}

		s=0;
		for(i=0; i<v.length; ++i) {
			s = s + v[i];
		}
		print("sum 1..", n, "=", s, "\n");
    print("Done!", "\n");
	}
}

// sum 1..4=10
// Done!
