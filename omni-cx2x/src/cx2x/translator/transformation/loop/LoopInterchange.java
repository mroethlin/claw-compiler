/*
 * This file is released under terms of BSD license
 * See LICENSE file for more information
 */

package cx2x.translator.transformation.loop;

import cx2x.translator.language.ClawLanguage;
import cx2x.translator.language.helper.TransformationHelper;
import cx2x.translator.language.helper.accelerator.AcceleratorHelper;
import cx2x.xcodeml.helper.*;
import cx2x.xcodeml.xelement.*;
import cx2x.xcodeml.transformation.*;
import cx2x.xcodeml.exception.*;

import xcodeml.util.XmOption;

import java.util.List;

/**
 * A LoopInterchange transformation is a an independent transformation. It allow
 * to reorder nested loops up to three levels.
 *
 * @author clementval
 */

public class LoopInterchange extends Transformation {

  private List<String> _newOrderOption = null;

  private XdoStatement _loopLevel0 = null;
  private XdoStatement _loopLevel1 = null;
  private XdoStatement _loopLevel2 = null;

  private String _baseLoop0 = null;
  private String _baseLoop1 = null;
  private String _baseLoop2 = null;
  private String _newLoop0 = null;
  private String _newLoop1 = null;
  private String _newLoop2 = null;

  // New ordering of the loops. Values are initial position.
  private int _loopNewPos0 = 0;
  private int _loopNewPos1 = 1;
  private int _loopNewPos2 = 2;

  private final ClawLanguage _claw;

  /**
   * Constructs a new LoopInterchange triggered from a specific pragma.
   * @param directive The directive that triggered the loop interchange
   *                  transformation.
   */
  public LoopInterchange(ClawLanguage directive){
    super(directive);
    _claw = directive;
    _newOrderOption = directive.getIndexes();
  }

  /**
   * Apply the transformation.
   * @param xcodeml        The XcodeML on which the transformations are applied.
   * @param transformer    The transformer used to applied the transformations.
   * @param transformation Only for dependent transformation. The other
   *                       transformation part of the transformation.
   * @throws IllegalTransformationException if the tranformation cannot be
   * applied.
   */
  @Override
  public void transform(XcodeProgram xcodeml, Transformer transformer,
                        Transformation transformation)
      throws IllegalTransformationException
  {

    analyze(xcodeml, transformer);

    if(XmOption.isDebugOutput()){
      System.out.println("loop-interchange transformation");
      System.out.println("  loop 0: " + _loopLevel0.getFormattedRange());
      System.out.println("  loop 1: " + _loopLevel1.getFormattedRange());
      if(_loopLevel2 != null){
        System.out.println("  loop 2: " + _loopLevel2.getFormattedRange());
      }
    }

    /* To perform the loop interchange, only the ranges and iteration
     * variables are swapped
     */
    if(_loopLevel1 != null && _loopLevel2 == null){
      // Loop interchange between 2 loops
      swapLoops(_loopLevel0, _loopLevel1);
    } else if (_loopLevel1 != null && _loopLevel2 != null){
      // loop interchange between 3 loops with new-order
      computeLoopNewPosition();
      printTransformDebugInfo();

      if(needDoubleSwap()){
        // Case 201
        if (_loopNewPos0 == 2 && _loopNewPos1 == 0 && _loopNewPos2 == 1){
          printTransformSwapInfo(201);
          swapLoops(_loopLevel0, _loopLevel2);
          swapLoops(_loopLevel0, _loopLevel1);
        // Case 120
        } else if (_loopNewPos0 == 1 && _loopNewPos1 == 2 && _loopNewPos2 == 0){
          printTransformSwapInfo(120);
          swapLoops(_loopLevel0, _loopLevel2);
          swapLoops(_loopLevel1, _loopLevel2);
        }
      } else {
        // Only one loop swap is needed
        XdoStatement from = null;
        XdoStatement to = null;
        if(_loopNewPos0 == 0){ // Loop 0 stay in place 0
          from = _loopLevel1;
          to = _loopLevel2;
        } else if(_loopNewPos1 == 1){ // Loop 1 stay in place 1
          from = _loopLevel0;
          to = _loopLevel2;
        } else if(_loopNewPos2 == 2){ // Loop 2 stay in place 2
          from = _loopLevel0;
          to = _loopLevel1;
        }
        swapLoops(from, to);
      }
    }


    // Generate accelerator pragmas if needed
    AcceleratorHelper.generateAdditionalDirectives(_claw, xcodeml, _loopLevel0);

    this.transformed();
  }

  /**
   * Swap two do statement. Induction variable and range are swapped.
   * @param loop1 The first do statement.
   * @param loop2 The second do statement.
   */
  private void swapLoops(XdoStatement loop1, XdoStatement loop2){
    // Save most inner loop iteration variable and range
    XloopIterationRange tmpIterationRange = loop2.getIterationRange().cloneObject();

    // Set the range of loop 0 to loop 2
    loop2.setNewRange(loop1.getIterationRange());
    // Remove the previous range of loop 2
    loop2.deleteRangeElements();
    // Set new range of loop 2 to loop 0
    loop1.setNewRange(tmpIterationRange);
    // Remove the previous range of loop 0
    loop1.deleteRangeElements();

    // recompute the range elements
    loop2.findRangeElements();
    loop1.findRangeElements();

  }

  /**
   * Check whether the transformation needs a single swap transformation or a
   * double swap transformation.
   * @return True if the transformation needs a double swap. False if a single
   * swap is needed.
   */
  private boolean needDoubleSwap(){
    return (_loopNewPos0 == 2 && _loopNewPos1 == 0 && _loopNewPos2 == 1) ||
        (_loopNewPos0 == 1 && _loopNewPos1 == 2 && _loopNewPos2 == 0);
  }

  /**
   * Based on the new ordering option, compute the new position of the different
   * do statement.
   */
  private void computeLoopNewPosition(){
    if (_baseLoop0.equals(_newLoop1)){
      _loopNewPos0 = 1;
    } else if (_baseLoop0.equals(_newLoop2)){
      _loopNewPos0 = 2;
    }

    if (_baseLoop1.equals(_newLoop0)){
      _loopNewPos1 = 0;
    } else if (_baseLoop1.equals(_newLoop2)){
      _loopNewPos1 = 2;
    }

    if (_baseLoop2.equals(_newLoop0)){
      _loopNewPos2 = 0;
    } else if (_baseLoop2.equals(_newLoop1)){
      _loopNewPos2 = 1;
    }
  }

  /**
   * Loop fusion analysis:
   * - Find the different do statement that will be reordered.
   * - Check the validity of the new ordering option.
   * @param xcodeml      The XcodeML on which the transformations are applied.
   * @param transformer  The transformer used to applied the transformations.
   * @return True if the transformation can be performed. False otherwise.
   */
  @Override
  public boolean analyze(XcodeProgram xcodeml, Transformer transformer){
    // Find next loop after pragma
    _loopLevel0 = XelementHelper.findNextDoStatement(_claw.getPragma());

    if(_loopLevel0 == null){
      xcodeml.addError("top level loop not found",
          _claw.getPragma().getLineNo());
      return false;
    }

    _loopLevel1 = XelementHelper.findDoStatement(_loopLevel0.getBody(), false);
    if(_loopLevel1 == null){
      return false;
    }

    if(_newOrderOption != null){
      if(_newOrderOption.size() != 3){
        xcodeml.addError("new-order option has not enough parameters",
            _claw.getPragma().getLineNo());
      }

      _loopLevel2 = XelementHelper.findDoStatement(_loopLevel1.getBody(), false);
      if(_loopLevel2 == null){
        return false;
      }

      _baseLoop0 = _loopLevel0.getInductionVariable();
      _baseLoop1 = _loopLevel1.getInductionVariable();
      _baseLoop2 = _loopLevel2.getInductionVariable();

      if(!checkNewOrderOption(xcodeml, _newOrderOption)){
        return false;
      }

      _newLoop0 = _newOrderOption.get(0);
      _newLoop1 = _newOrderOption.get(1);
      _newLoop2 = _newOrderOption.get(2);
    }


    return true;
  }

  /**
   * Check the vailidity of the new ordering option.
   * @param xcodeml The XcodeML object.
   * @param idxs    List containing the induction variables.
   * @return True if the new ordering is valid. False otherwise.
   */
  private boolean checkNewOrderOption(XcodeProgram xcodeml, List<String> idxs){
    for(String idx : idxs){
      if(!idx.equals(_baseLoop0) && !idx.equals(_baseLoop1)
        && !idx.equals(_baseLoop2))
      {
        xcodeml.addError("invalid induction variable in new-order option. "
          + idx, _claw.getPragma().getLineNo());
        return false;
      }
    }
    return true;
  }

  /**
   * @see Transformation#canBeTransformedWith(Transformation)
   * @return Always false as independent transformation are applied one by one.
   */
  @Override
  public boolean canBeTransformedWith(Transformation transformation){
    // independent transformation
    return false;
  }

  /**
   * Print some useful debugging information
   */
  private void printTransformDebugInfo(){
    if(XmOption.isDebugOutput()){
      System.out.println("  transform from " + _baseLoop0 + "," + _baseLoop1
        + "," + _baseLoop2 + " (012) to " + _newLoop0 + "," + _newLoop1 + "," +
        _newLoop2 + " (" + _loopNewPos0 + _loopNewPos1 +
          _loopNewPos2 + ")");

      if(needDoubleSwap()){
        System.out.println("    double swap required");
      }
    }
  }

  /**
   * Print information for double swap cases
   * @param swapCase Integer representing the new ordering (120 or 201)
   */
  private void printTransformSwapInfo(int swapCase) {
    if(XmOption.isDebugOutput() && swapCase == 120){
      System.out.println("    swap 1: " + _baseLoop0 + " <--> " + _baseLoop2);
      System.out.println("    swap 2: " + _baseLoop1 + " <--> " + _baseLoop0);
    } else if (XmOption.isDebugOutput() && swapCase == 201){
      System.out.println("    swap 1: " + _baseLoop0 + " <--> " + _baseLoop2);
      System.out.println("    swap 2: " + _baseLoop2 + " <--> " + _baseLoop1);
    }
  }


}
