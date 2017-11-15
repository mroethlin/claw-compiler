/*
 * This file is released under terms of BSD license
 * See LICENSE file for more information
 */
package cx2x.xcodeml.language;

import cx2x.xcodeml.xnode.Xcode;
import cx2x.xcodeml.xnode.XcodeProgram;
import cx2x.xcodeml.xnode.Xnode;
import helper.XmlHelper;
import org.junit.Test;

import static junit.framework.TestCase.*;

/**
 * Test methods of the AnalyzedPragma class.
 *
 * @author clementval
 */
public class AnalyzedPragmaTest {

  @Test
  public void ctorTest() {
    XcodeProgram xcodeml = XmlHelper.getDummyXcodeProgram();
    Xnode p1 = xcodeml.createNode(Xcode.F_PRAGMA_STATEMENT);
    p1.setValue("acc parallel");
    Xnode p2 = xcodeml.createNode(Xcode.F_PRAGMA_STATEMENT);
    p2.setValue("acc end parallel");

    AnalyzedPragma ap1 = new AnalyzedPragma(p1);
    assertFalse(ap1.isEndPragma());
    assertNotNull(ap1.getPragma());
    assertEquals("acc parallel", ap1.getPragma().value());

    ap1.setEndPragma();
    assertTrue(ap1.isEndPragma());

    AnalyzedPragma ap2 = new AnalyzedPragma();
    assertFalse(ap2.isEndPragma());
    assertNull(ap2.getPragma());
    ap2.setPragma(p2);
    assertEquals("acc end parallel", ap2.getPragma().value());
  }
}
