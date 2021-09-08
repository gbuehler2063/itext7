/*
    This file is part of the iText (R) project.
    Copyright (c) 1998-2021 iText Group NV
    Authors: iText Software.

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU Affero General Public License version 3
    as published by the Free Software Foundation with the addition of the
    following permission added to Section 15 as permitted in Section 7(a):
    FOR ANY PART OF THE COVERED WORK IN WHICH THE COPYRIGHT IS OWNED BY
    ITEXT GROUP. ITEXT GROUP DISCLAIMS THE WARRANTY OF NON INFRINGEMENT
    OF THIRD PARTY RIGHTS

    This program is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.
    See the GNU Affero General Public License for more details.
    You should have received a copy of the GNU Affero General Public License
    along with this program; if not, see http://www.gnu.org/licenses or write to
    the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
    Boston, MA, 02110-1301 USA, or download the license from the following URL:
    http://itextpdf.com/terms-of-use/

    The interactive user interfaces in modified source and object code versions
    of this program must display Appropriate Legal Notices, as required under
    Section 5 of the GNU Affero General Public License.

    In accordance with Section 7(b) of the GNU Affero General Public License,
    a covered work must retain the producer line in every PDF that is created
    or manipulated using iText.

    You can be released from the requirements of the license by purchasing
    a commercial license. Buying such a license is mandatory as soon as you
    develop commercial activities involving the iText software without
    disclosing the source code of your own applications.
    These activities include: offering paid services to customers as an ASP,
    serving PDFs on the fly in a web application, shipping iText with a closed
    source product.

    For more information, please contact iText Software Corp. at this
    address: sales@itextpdf.com
 */
package com.itextpdf.commons.actions.contexts;

import com.itextpdf.commons.actions.NamespaceConstant;
import com.itextpdf.test.ExtendedITextTest;
import com.itextpdf.test.annotations.type.UnitTest;

import java.util.Arrays;
import java.util.Collections;
import org.junit.Assert;
import org.junit.Test;
import org.junit.experimental.categories.Category;

@Category(UnitTest.class)
public class ContextManagerTest extends ExtendedITextTest {

    @Test
    public void getRecognisedNamespaceForSpecificNamespaceTest() {
        String outerNamespaces = NamespaceConstant.ITEXT.toLowerCase();
        String innerNamespaces = NamespaceConstant.PDF_HTML.toLowerCase();

        Assert.assertTrue(innerNamespaces.startsWith(outerNamespaces));

        ContextManager managerOuterBeforeInner = new ContextManager();
        managerOuterBeforeInner.registerGenericContextForProducts(Collections.singletonList(outerNamespaces),
                Collections.<String>emptyList());
        managerOuterBeforeInner.registerGenericContextForProducts(Collections.singletonList(innerNamespaces),
                Collections.<String>emptyList());

        Assert.assertEquals(outerNamespaces,
                managerOuterBeforeInner.getRecognisedNamespace(outerNamespaces));
        Assert.assertEquals(innerNamespaces,
                managerOuterBeforeInner.getRecognisedNamespace(innerNamespaces));

        ContextManager managerInnerBeforeOuter = new ContextManager();
        managerInnerBeforeOuter.registerGenericContextForProducts(Collections.singletonList(innerNamespaces),
                Collections.<String>emptyList());
        managerInnerBeforeOuter.registerGenericContextForProducts(Collections.singletonList(outerNamespaces),
                Collections.<String>emptyList());

        Assert.assertEquals(outerNamespaces,
                managerInnerBeforeOuter.getRecognisedNamespace(outerNamespaces));
        Assert.assertEquals(innerNamespaces,
                managerInnerBeforeOuter.getRecognisedNamespace(innerNamespaces));
    }

    @Test
    public void notRegisteredNamespaceTest() {
        String notRegisteredNamespace = "com.hello.world";

        Assert.assertNull(ContextManager.getInstance().getRecognisedNamespace(notRegisteredNamespace));
    }

    @Test
    public void unregisterNamespaceTest() {
        String testNamespace = "com.hello.world";
        ContextManager manager = new ContextManager();
        Assert.assertNull(manager.getRecognisedNamespace(testNamespace));
        manager.registerGenericContextForProducts(Arrays.asList(testNamespace),
                Arrays.asList("myProduct"));
        Assert.assertEquals(testNamespace,
                manager.getRecognisedNamespace(testNamespace + ".MyClass"));
        manager.unregisterGenericContextForProducts(Arrays.asList(testNamespace));
        Assert.assertNull(manager.getRecognisedNamespace(testNamespace));
    }

    @Test
    public void registeredNamespaceTest() {
        String registeredNamespace = NamespaceConstant.CORE_LAYOUT + "custompackage";

        Assert.assertEquals(NamespaceConstant.CORE_LAYOUT.toLowerCase(),
                ContextManager.getInstance().getRecognisedNamespace(registeredNamespace));
    }
}