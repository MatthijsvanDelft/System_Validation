/** This class encapsulates lookup table scales. */

class LookupScale {
	
	/** Stores the scale (so called) break points.
	  * Scales are required to be strictly monotone,
	  * with raising values. */
	int[] values;

	// INVARIANT(S)
	//@ invariant this.values.length > 1;
	
	// This invariant causes time-out
	//@ invariant (\forall int k; k>0 && k<this.values.length; this.values[k-1] < this.values[k]);

	
	/**
	 * Construct the scale with predefined break points
	 * @param values the array with break point values
	 */
	// CONTRACT 
	/*@ normal_behavior
	  @ requires values.length > 1;
	  @ requires (\forall int i; i>0 && i < values.length; values[i] > values[i - 1]);
	  @ ensures this.values == values;
	  @ assignable this.values;
	  @*/
	LookupScale(int[] values) {
		this.values = values;
	}
	
	/**
	 * Construct a linear scale that has size break points equally
	 * distributed between min and max values. 
	 * @param min minimal value of the scale
	 * @param max maximal value of the scale
	 * @param size number of break points in the scale
	 */  
	 
	// CONTRACT 
	/*@ normal_behavior
	  @ requires min < max;
	  @ requires size > 1;
	  @ ensures this.values.length == size;
	  @ ensures this.values[0] == min;
	  @ assignable this.values[*];
	  @*/
	LookupScale(int min, int max, int size) {
		this.values = new int[size];
		int chunk = (max - min) / (size - 1);
		//@ assume chunk > 0;
		this.values[0] = min;
		
		// loop_inv 4 (forall) causes time-out!

		// ERROR: compile internal error when using decreases??\
		//@ loop_invariant i>=1 && i<=this.values.length;
		//@ loop_invariant (\forall int k; k>0 && k<i; this.values[k-1] < this.values[k]);
		// decreases this.values.length - i;
		for(int i=1; i<this.values.length; i++) {
		  this.values[i] = this.values[i-1] + chunk;
		}
		
		
	}	

	/**
	 * Looks up a sensor value in the scale and returns the scale index
	 * corresponding to the position of the sensor value in the scale. 
	 * @param sv the sensor value that should be looked up the scale
	 * @return the scale index (integral and fractional part)
	 */
	// ensures \result.intPart >= 0 && \result.intPart < this.values.length;
	 //  ensures \result.fracPart >=0 && \result.fracPart < 100; 
	 // ensures \result.intPart == 0 || this.values[\result.intPart] <= sv.getValue();
	  // ensures \result.intPart == this.values.length - 1 || sv.getValue() < this.values[\result.intPart+1];
	
	
	// CONTRACT
	/*@ normal_behavior
	  @ requires sv.getValue() < this.values[0];
	  @ ensures \result.intPart == 0 && \result.fracPart == 0;
	  @ ensures \result.size == this.values.length;
	  @
	  @ also
	  @
	  @ normal_behavior
	  @ requires sv.getValue() >= this.values[0] && sv.getValue() < this.values[values.length -1];
	  @ ensures \result.intPart >=0 && \result.intPart < this.values.length;
	  @ ensures \result.fracPart >= 0 && \result.fracPart < 100;
	  @ ensures \result.size == this.values.length;
	  @
	  @ also
	  @
	  @ normal_behavior
	  @ requires sv.getValue() >= values[this.values.length-1];
	  @ ensures \result.intPart == this.values.length -1;
	  @ ensures \result.fracPart == 0;
	  @ ensures \result.size == this.values.length;
	  @*/
	   /*@ pure @*/ ScaleIndex lookupValue(SensorValue sv) {
		   int v = sv.getValue();
		// First get the integral part
			// The most convenient way to lookup scales is from the end
			int intPart = this.values.length - 1;
			//@ loop_invariant intPart>=-1;
		    //@ loop_invariant intPart<this.values.length;
			// No decreases because intPart can remain if directly break.
			while(intPart >= 0) {
				if(v >= this.values[intPart]) {
					break;
				}
				intPart--;
			}
			// ASSERTION
			//! MISTAKE: can be minus but should be put back to zero!
			if (intPart < 0) intPart = 0;
			//@ assert intPart >= 0;
			int fracPart = 0;
			// Check border cases
			if(intPart == this.values.length - 1 || v < this.values[0]) {
				// ASSERTION(S)
				//@ assert intPart == this.values.length - 1 || v < this.values[0];
				//@ assert fracPart == 0;
				return new ScaleIndex(intPart, fracPart, this.values.length);
			}
			// Then calculate the fractional part
			fracPart = (v - this.values[intPart]) * 100 / (this.values[intPart+1] - this.values[intPart]);
			// ASSERTION(S)
			//@ assert intPart >= 0 && intPart < this.values.length;
			//@ assert fracPart >= 0 && fracPart < 100;
			return new ScaleIndex(intPart, fracPart, this.values.length);
	}

	/**
	 * Provide a human readable version of this object, makes 
	 * the output of JMLUnitNG more readable.
	 */
	//@ skipesc;
	public String toString() {
		String r = "Scale of size "+this.values.length+": [";
		for(int i = 0; i<this.values.length; i++) {
			r += ""+(i==0 ? "" : ", ")+values[i];
		}
		r += "]";
		return r;
	}

}
