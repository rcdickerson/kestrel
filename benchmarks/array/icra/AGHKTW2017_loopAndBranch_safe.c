/* @KESTREL
 * pre:   left.low == right.low;
 * left:  loopAndBranch_safe;
 * right: loopAndBranch_safe;
 * post:  left.tick == right.tick;
 */

/* Source: Timos Antonopoulos, Paul Gazzillo, Michael Hicks, Eric Koskinen,
   Tachio Terauchi, Shiyi Wei: Decomposition Instead of Self-Composition for
   Proving the Absence of Timing Channels.  PLDI 2017 */
void loopAndBranch_safe (int high, int low) {
    int i = low;
    int tick = 0;
    if (low < 0) {
	while (i > 0) {
	    tick = tick + 1;
	    i = i - 1;
	}
    } else {
	low = low + 10; // low is above 0
	if (low >= 10) {
	    int j = low;
	    while (j > 0) {
		j = j - 1;
		tick = tick + 1;
	    }
	} else {
	    if (high < 0) { //this branch would reveal info, but it is infeasible
		int k = low;
		while (k>0) {
		    k = k - 1;
		    tick = tick + 1;
		}
	    }
	}
    }
}
