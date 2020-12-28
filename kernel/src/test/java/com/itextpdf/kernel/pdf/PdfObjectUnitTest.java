/*
    This file is part of the iText (R) project.
    Copyright (c) 1998-2020 iText Group NV
    Authors: iText Software.

    This program is offered under a commercial and under the AGPL license.
    For commercial licensing, contact us at https://itextpdf.com/sales.  For AGPL licensing, see below.

    AGPL licensing:
    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU Affero General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Affero General Public License for more details.

    You should have received a copy of the GNU Affero General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */
package com.itextpdf.kernel.pdf;

import com.itextpdf.io.source.ByteArrayOutputStream;
import com.itextpdf.kernel.PdfException;
import com.itextpdf.kernel.exceptions.KernelExceptionMessageConstant;
import com.itextpdf.test.ExtendedITextTest;
import com.itextpdf.test.annotations.type.UnitTest;

import java.io.IOException;
import org.junit.Rule;
import org.junit.Test;
import org.junit.experimental.categories.Category;
import org.junit.rules.ExpectedException;

@Category(UnitTest.class)
public class PdfObjectUnitTest extends ExtendedITextTest {
    public static final String sourceFolder = "./src/test/resources/com/itextpdf/kernel/pdf/PdfObjectUnitTest/";

    @Rule
    public ExpectedException junitExpectedException = ExpectedException.none();

    @Test
    public void noWriterForMakingIndirectTest() throws IOException {
        junitExpectedException.expect(PdfException.class);
        junitExpectedException
                .expectMessage(KernelExceptionMessageConstant.THERE_IS_NO_ASSOCIATE_PDF_WRITER_FOR_MAKING_INDIRECTS);

        PdfDocument pdfDocument = new PdfDocument(new PdfReader(sourceFolder + "noWriterForMakingIndirect.pdf"));
        PdfDictionary pdfDictionary = new PdfDictionary();
        pdfDictionary.makeIndirect(pdfDocument);
    }

    @Test
    public void copyDocInReadingModeTest() throws IOException {
        junitExpectedException.expect(PdfException.class);
        junitExpectedException
                .expectMessage(KernelExceptionMessageConstant.CANNOT_COPY_TO_DOCUMENT_OPENED_IN_READING_MODE);

        PdfDocument pdfDocument = new PdfDocument(new PdfReader(sourceFolder + "copyDocInReadingMode.pdf"));
        PdfDictionary pdfDictionary = new PdfDictionary();
        pdfDictionary.processCopying(pdfDocument, true);
    }

    @Test
    public void copyIndirectObjectTest() {
        junitExpectedException.expect(PdfException.class);
        junitExpectedException.expectMessage(
                KernelExceptionMessageConstant.CANNOT_COPY_INDIRECT_OBJECT_FROM_THE_DOCUMENT_THAT_IS_BEING_WRITTEN);

        PdfDocument pdfDocument = new PdfDocument(new PdfWriter(new ByteArrayOutputStream()));
        PdfObject pdfObject = pdfDocument.getPdfObject(1);
        pdfObject.copyTo(pdfDocument, true);
    }

    @Test
    public void copyFlushedObjectTest() {
        junitExpectedException.expect(PdfException.class);
        junitExpectedException.expectMessage(KernelExceptionMessageConstant.CANNOT_COPY_FLUSHED_OBJECT);

        PdfDocument pdfDocument = new PdfDocument(new PdfWriter(new ByteArrayOutputStream()));
        PdfObject pdfObject = pdfDocument.getPdfObject(1);
        pdfObject.flush();
        pdfObject.copyContent(pdfObject, pdfDocument);
    }
}