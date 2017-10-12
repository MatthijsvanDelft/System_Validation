/**
 * An encapsulation class that stores the current value of a sensor readout.
 * The class is responsible for checking the sanity (staying within the 
 * allowable range) of the readouts and providing a fail-safe value in case
 * of failures.
 */
class SensorValue {

	int value;
	final int failSafe;
	final int minValue;
	final int maxValue;

	// INVARIANT(S)
	//@ invariant minValue <= maxValue;
	//@ invariant minValue <= value && value <= maxValue;
	//@ invariant failSafe >= minValue && failSafe <= maxValue;
	
	/**
	 * @param failSafe the default fail-safe value for this sensor
	 * @param minValue minimum allowable value for this sensor
	 * @param maxValue maximum allowable value for this sensor
	 */
	// CONTRACT
	/*@ normal_behavior
	  @ requires minValue <= failSafe;
	  @ requires failSafe <= maxValue;
	  @ requires minValue <= maxValue;
	  @ ensures this.failSafe == failSafe;
	  @ ensures this.minValue == minValue;
	  @ ensures this.maxValue == maxValue;
	  @ ensures this.value == failSafe;	  
	  @ assignable this.failSafe, this.minValue, this.maxValue, this.value;
	  @*/
	SensorValue(int failSafe, int minValue, int maxValue) {
		this.failSafe = failSafe;
		this.minValue = minValue;
		this.maxValue = maxValue;
		this.value = failSafe;
	}
	
	/**
	 * The newly read value is either within the allowable range
	 * or has to be substituted with a fail-safe. 
	 * @param newValue newly read value
	 */
	// CONTRACT
	/*@ normal_behavior
	  @ requires (newValue < this.minValue || newValue > this.maxValue);
	  @ ensures this.value == this.failSafe;
	  @ also
	  @ normal_behavior
	  @ requires (newValue >= this.minValue && newValue <= this.maxValue);
	  @ ensures this.value == newValue;
	  @*/
	void readSensor(int newValue) {
		if(newValue < this.minValue || newValue > this.maxValue) {
			this.value = this.failSafe;
		}else{
			this.value = newValue;
		}
	}
	
	/**
	 * @return the most recently read value
	 */
	// CONTRACT
	/*@ normal_behavior
	  @ ensures \result == this.value;
	  @*/
	/*@ pure @*/int getValue() {
		return this.value;
	}
	
	/**
	 * Provide a human readable version of this object, makes 
	 * the output of JMLUnitNG more readable.
	 */
	// skipesc;
	public String toString() {
		return "SensorValue <"+minValue+"-"+maxValue+", FS="+failSafe+"> = ["+value+"]";
	}
	
}
