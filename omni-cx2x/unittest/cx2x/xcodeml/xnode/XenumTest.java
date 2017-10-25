/*
 * This file is released under terms of BSD license
 * See LICENSE file for more information
 */

package cx2x.xcodeml.xnode;

import org.junit.Test;

import static org.junit.Assert.*;

/**
 * Testing methods from various enum class. Xattr, XbuiltInType, Xcode, Xintent,
 * Xscope.
 *
 * @author clementval
 */
public class XenumTest {

  @Test
  public void xAttrStringToEnumTest() {
    for(Xattr attrCode : Xattr.values()) {
      String rep = attrCode.toString();
      Xattr attr = Xattr.fromString(rep);
      assertEquals(attrCode, attr);
    }
  }

  @Test
  public void xIntentCtorTest() {
    assertEquals(Xintent.IN, Xintent.fromString("in"));
    assertEquals(Xintent.IN, Xintent.fromString("IN"));

    assertEquals(Xintent.OUT, Xintent.fromString("out"));
    assertEquals(Xintent.OUT, Xintent.fromString("OUT"));

    assertEquals(Xintent.INOUT, Xintent.fromString("inout"));
    assertEquals(Xintent.INOUT, Xintent.fromString("INOUT"));

    assertEquals(Xintent.INOUT, Xintent.fromString("inOUT"));

    assertEquals(Xintent.NONE, Xintent.fromString(null));
    assertEquals(Xintent.NONE, Xintent.fromString(""));

    assertEquals(Xname.INTENT_IN, Xintent.IN.toString());
    assertEquals(Xname.INTENT_OUT, Xintent.OUT.toString());
    assertEquals(Xname.INTENT_INOUT, Xintent.INOUT.toString());
    assertEquals("", Xintent.NONE.toString());
    assertEquals("", Xintent.ANY.toString());
  }

  @Test
  public void xIntentCheckTest() {
    Xintent intent1 = Xintent.IN;
    Xintent intent2 = Xintent.OUT;
    Xintent intent3 = Xintent.INOUT;
    Xintent intent4 = Xintent.NONE;
    Xintent any = Xintent.ANY;

    assertTrue(intent1.isIntentIn());
    assertFalse(intent2.isIntentIn());
    assertTrue(intent3.isIntentIn());
    assertFalse(intent4.isIntentIn());

    assertFalse(intent1.isIntentOut());
    assertTrue(intent2.isIntentOut());
    assertTrue(intent3.isIntentOut());
    assertFalse(intent4.isIntentOut());

    assertTrue(intent1.isIntent());
    assertTrue(intent2.isIntent());
    assertTrue(intent3.isIntent());
    assertFalse(intent4.isIntent());

    assertTrue(intent1.isCompatible(intent1));
    assertFalse(intent1.isCompatible(intent2));
    assertTrue(intent1.isCompatible(intent3));
    assertFalse(intent1.isCompatible(intent4));
    assertTrue(intent1.isCompatible(any));

    assertFalse(intent2.isCompatible(intent1));
    assertTrue(intent2.isCompatible(intent2));
    assertTrue(intent2.isCompatible(intent3));
    assertFalse(intent2.isCompatible(intent4));
    assertTrue(intent2.isCompatible(any));

    assertTrue(intent3.isCompatible(intent1));
    assertTrue(intent3.isCompatible(intent2));
    assertTrue(intent3.isCompatible(intent3));
    assertFalse(intent3.isCompatible(intent4));
    assertTrue(intent3.isCompatible(any));

    assertFalse(intent4.isCompatible(intent1));
    assertFalse(intent4.isCompatible(intent2));
    assertFalse(intent4.isCompatible(intent3));
    assertTrue(intent4.isCompatible(intent4));
    assertTrue(intent4.isCompatible(any));

    assertTrue(any.isCompatible(intent1));
    assertTrue(any.isCompatible(intent2));
    assertTrue(any.isCompatible(intent3));
    assertTrue(any.isCompatible(intent4));
    assertTrue(any.isCompatible(any));

    assertFalse(intent1.isCompatible(null));
    assertFalse(intent2.isCompatible(null));
    assertFalse(intent3.isCompatible(null));
    assertFalse(intent4.isCompatible(null));
    assertFalse(any.isCompatible(null));
  }

  @Test
  public void xScopeCctorTest() {
    assertEquals(Xscope.LOCAL, Xscope.fromString("local"));
    assertEquals(Xscope.GLOBAL, Xscope.fromString("global"));
    assertEquals(Xscope.PARAM, Xscope.fromString("param"));
    assertEquals(Xscope.LOCAL, Xscope.fromString("LOCAL"));
    assertEquals(Xscope.GLOBAL, Xscope.fromString("GLOBAL"));
    assertEquals(Xscope.PARAM, Xscope.fromString("PARAM"));

    assertNull(Xscope.fromString(""));
    assertNull(Xscope.fromString(null));

    assertEquals(Xname.SCOPE_LOCAL, Xscope.LOCAL.toString());
    assertEquals(Xname.SCOPE_GLOBAL, Xscope.GLOBAL.toString());
    assertEquals(Xname.SCOPE_PARAM, Xscope.PARAM.toString());
  }

  @Test
  public void xBuiltInTypeCtorTest() {
    assertEquals(XbuiltInType.NONE, XbuiltInType.fromString(null));
    assertEquals(XbuiltInType.NONE, XbuiltInType.fromString(""));
    assertEquals(XbuiltInType.INT,
        XbuiltInType.fromString(Xname.TYPE_F_INT));
    assertEquals(XbuiltInType.REAL,
        XbuiltInType.fromString(Xname.TYPE_F_REAL));
    assertEquals(XbuiltInType.COMPLEX,
        XbuiltInType.fromString(Xname.TYPE_F_COMPLEX));
    assertEquals(XbuiltInType.LOGICAL,
        XbuiltInType.fromString(Xname.TYPE_F_LOGICAL));
    assertEquals(XbuiltInType.CHAR,
        XbuiltInType.fromString(Xname.TYPE_F_CHAR));
    assertEquals(XbuiltInType.VOID,
        XbuiltInType.fromString(Xname.TYPE_F_VOID));

    assertEquals(Xname.TYPE_F_INT, XbuiltInType.INT.toString());
    assertEquals(Xname.TYPE_F_REAL, XbuiltInType.REAL.toString());
    assertEquals(Xname.TYPE_F_COMPLEX, XbuiltInType.COMPLEX.toString());
    assertEquals(Xname.TYPE_F_LOGICAL, XbuiltInType.LOGICAL.toString());
    assertEquals(Xname.TYPE_F_CHAR, XbuiltInType.CHAR.toString());
    assertEquals(Xname.TYPE_F_VOID, XbuiltInType.VOID.toString());
  }

  @Test
  public void xStorageClassCtorTest() {
    assertEquals(XstorageClass.NONE, XstorageClass.fromString(null));
    assertEquals(XstorageClass.NONE, XstorageClass.fromString(""));
    assertEquals(XstorageClass.AUTO,
        XstorageClass.fromString(Xname.SCLASS_AUTO));
    assertEquals(XstorageClass.F_LOCAL,
        XstorageClass.fromString(Xname.SCLASS_F_LOCAL));
    assertEquals(XstorageClass.F_PARAM,
        XstorageClass.fromString(Xname.SCLASS_F_PARAM));
    assertEquals(XstorageClass.F_FUNC,
        XstorageClass.fromString(Xname.SCLASS_F_FUNC));
    assertEquals(XstorageClass.EXTERN,
        XstorageClass.fromString(Xname.SCLASS_EXTERN));
    assertEquals(XstorageClass.EXTERN_DEF,
        XstorageClass.fromString(Xname.SCLASS_EXTERN_DEF));
    assertEquals(XstorageClass.LABEL,
        XstorageClass.fromString(Xname.SCLASS_LABEL));
    assertEquals(XstorageClass.PARAM,
        XstorageClass.fromString(Xname.SCLASS_PARAM));

    assertEquals(Xname.SCLASS_AUTO, XstorageClass.AUTO.toString());
    assertEquals(Xname.SCLASS_EXTERN, XstorageClass.EXTERN.toString());
    assertEquals(Xname.SCLASS_EXTERN_DEF, XstorageClass.EXTERN_DEF.toString());
    assertEquals(Xname.SCLASS_F_LOCAL, XstorageClass.F_LOCAL.toString());
    assertEquals(Xname.SCLASS_F_FUNC, XstorageClass.F_FUNC.toString());
    assertEquals(Xname.SCLASS_F_PARAM, XstorageClass.F_PARAM.toString());
    assertEquals(Xname.SCLASS_LABEL, XstorageClass.LABEL.toString());
    assertEquals(Xname.SCLASS_PARAM, XstorageClass.PARAM.toString());
  }

  @Test
  public void xCodeStringToEnumTest() {
    for(Xcode opcode : Xcode.values()) {
      String rep = opcode.toString();
      Xcode code = Xcode.fromString(rep);
      assertEquals(opcode, code);
    }
  }
}
