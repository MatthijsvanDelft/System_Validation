/** This class encapsulates a lookup table that is linear, that is,
 *  the output values are evenly distributed with respect to the scale.
 *  Note that this lookup table does not store its size (that is, scale indexes
 *  of arbitrary sizes can be used to look up values in this table). 
 */
class LookupTableLinear {

	/** The start (or minimal) value of the table. */
	int startValue;
	
	/** The value range of the table. */
	int range;
	
	// INVARIANT
	//  invariant range > 0;
	
	/**
	 * Constructs a new linear lookup table
	 * @param startValue the starting/minimum lookup value
	 * @param range the value range
	 */
	// CONTRACT				startVAlue && range ???
	/*@ normal_behavior
	  @ requires range > 0;
	  @ ensures this.startValue == startValue;
	  @ ensures this.range == range;
	  @ assignable this.startValue, this.range;
	  @*/
	LookupTableLinear(int startValue, int range) {
		this.startValue = startValue;
		this.range = range;
	}
	
	// CONTRACT
	/*@ normal_behavior
	  @ ensures \result == (this.startValue + (range * ((si.getIntPart()*100 + si.getFracPart())/si.getSize())) / 100);
	  @*/
	/*@ pure @*/ int getValue(ScaleIndex si) {
		return this.startValue + (range * ((si.getIntPart()*100 + si.getFracPart())/si.getSize())) / 100;
	}
}
