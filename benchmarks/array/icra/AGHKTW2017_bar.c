/* @KESTREL
 * pre:   left.low == right.low;
 * left:  bar;
 * right: bar;
 * post:  left.tick == right.tick;
 */

/* Source: Timos Antonopoulos, Paul Gazzillo, Michael Hicks, Eric Koskinen,
   Tachio Terauchi, Shiyi Wei: Decomposition Instead of Self-Composition for
   Proving the Absence of Timing Channels.  PLDI 2017 */
void bar (int high, int low) {
    int tick = 0;
    int i;
    if (low > 0) {
	i = 0;
	while (i < low) {
	    i = i + 1;
	    tick = tick + 1;
	}
	while (i > 0) {
	    i = i - 1;
	    tick = tick + 1;
	}
    } else {
	if (high == 0) {
	    i = 5;
	} else {
	    i = 0;
	    i = i + 1;
	}
    }
}
