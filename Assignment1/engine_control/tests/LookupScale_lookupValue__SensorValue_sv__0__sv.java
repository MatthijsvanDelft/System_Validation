/*
 * Test data strategy for LookupScale.
 *
 * Generated by JMLUnitNG 1.4 (116/OpenJML-20131218-REV3178), 2017-10-06 14:46 +0200.
 * (do not modify this comment, it is used by JMLUnitNG clean-up routines)
 */

import org.jmlspecs.jmlunitng.iterator.ObjectArrayIterator;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;

/**
 * Test data strategy for LookupScale. Provides
 * test values for parameter "SensorValue sv" 
 * of method "ScaleIndex lookupValue(SensorValue)". 
 * 
 * @author JMLUnitNG 1.4 (116/OpenJML-20131218-REV3178)
 * @version 2017-10-06 14:46 +0200
 */
public /*@ nullable_by_default */ class LookupScale_lookupValue__SensorValue_sv__0__sv
  extends LookupScale_ClassStrategy_SensorValue {
  /**
   * @return local-scope values for parameter 
   *  "SensorValue sv".
   */
  public RepeatedAccessIterator<?> localValues() {
    return new ObjectArrayIterator<Object>
    (new Object[]
     {
    		 //Lower boundary - minValue
    		 new SensorValue(600, 599, 8000),
    	     new SensorValue(600, 600, 8000),
    	     new SensorValue(601, 601, 8000),
    	     
    	     //Upper boundary - maxValue
    	     new SensorValue(2000, 600, 7999),
    	     new SensorValue(2000, 600, 8000),
    	     new SensorValue(2000, 600, 8001),
    	     
    	     //Test lower/higher and normal values
    	     new SensorValue(2000, 600, 9000),
    	     new SensorValue(2000, 0, 7999),
    	     new SensorValue(2000, 300, 4000),
    	     
    	     //Failsafe test
    	     new SensorValue(600, 600, 8000),
    	     new SensorValue(8000, 600, 8000),
    	     new SensorValue(1000, 600, 8000)
     });
  }

  /**
   * Constructor.
   * The use of reflection can be controlled here for  
   * "SensorValue sv" of method "ScaleIndex lookupValue(SensorValue)" 
   * by changing the parameters to <code>setReflective</code>
   * and <code>setMaxRecursionDepth<code>.
   * In addition, the data generators used can be changed by adding 
   * additional data class lines, or by removing some of the automatically 
   * generated ones. Since this is the lowest level of strategy, the 
   * behavior will be exactly as you specify here if you clear the existing 
   * list of classes first.
   *
   * @see NonPrimitiveStrategy#addDataClass(Class<?>)
   * @see NonPrimitiveStrategy#clearDataClasses()
   * @see ObjectStrategy#setReflective(boolean)
   * @see ObjectStrategy#setMaxRecursionDepth(int)
   */
  public LookupScale_lookupValue__SensorValue_sv__0__sv() {
    super();
    // uncomment to control the maximum reflective instantiation
    // recursion depth, 0 by default
    // setMaxRecursionDepth(0);
  }
}
