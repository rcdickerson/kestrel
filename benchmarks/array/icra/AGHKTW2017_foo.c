/* @KESTREL
 * pre:   left.low == right.low;
 * left:  foo;
 * right: foo;
 * post:  left.tick == right.tick;
 */

/* Source: Timos Antonopoulos, Paul Gazzillo, Michael Hicks, Eric Koskinen,
   Tachio Terauchi, Shiyi Wei: Decomposition Instead of Self-Composition for
   Proving the Absence of Timing Channels.  PLDI 2017 */
void foo (int high, int low) {
    int tick = 0;
    int i;
    if (high == 0) {
	i = 0;
	while(i < low) {
	    i = i + 1;
	    tick = tick + 1;
	}
    } else {
	i = low;
	while(i > 0) {
	    i = i - 1;
	    tick = tick + 1;
	}
    }
}
