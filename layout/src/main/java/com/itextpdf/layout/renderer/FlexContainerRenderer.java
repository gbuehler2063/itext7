/*

    This file is part of the iText (R) project.
    Copyright (c) 1998-2021 iText Group NV
    Authors: Bruno Lowagie, Paulo Soares, et al.

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
package com.itextpdf.layout.renderer;

import com.itextpdf.kernel.geom.Rectangle;
import com.itextpdf.layout.borders.Border;
import com.itextpdf.layout.element.Div;
import com.itextpdf.layout.layout.LayoutContext;
import com.itextpdf.layout.layout.LayoutResult;
import com.itextpdf.layout.minmaxwidth.MinMaxWidth;
import com.itextpdf.layout.minmaxwidth.MinMaxWidthUtils;
import com.itextpdf.layout.property.Property;
import com.itextpdf.layout.property.UnitValue;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class FlexContainerRenderer extends DivRenderer {

    private List<List<FlexItemInfo>> lines;

    /**
     * Creates a FlexContainerRenderer from its corresponding layout object.
     * @param modelElement the {@link com.itextpdf.layout.element.Div} which this object should manage
     */
    public FlexContainerRenderer(Div modelElement) {
        super(modelElement);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public IRenderer getNextRenderer() {
        return new FlexContainerRenderer((Div) modelElement);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public LayoutResult layout(LayoutContext layoutContext) {
        Rectangle layoutContextRectangle = layoutContext.getArea().getBBox();
        for (final IRenderer childRenderer : this.getChildRenderers()) {
            if (childRenderer instanceof AbstractRenderer) {
                final AbstractRenderer abstractChildRenderer = (AbstractRenderer) childRenderer;
                abstractChildRenderer.setParent(this);
            }
        }
        Float containerWidth = retrieveWidth(layoutContextRectangle.getWidth());
        if (containerWidth == null) {
            containerWidth = layoutContextRectangle.getWidth();
        }
        Float containerHeight = retrieveHeight();
        if (containerHeight == null) {
            containerHeight = layoutContextRectangle.getHeight();
        }
        lines = FlexUtil.calculateChildrenRectangles(
                new Rectangle((float) containerWidth, (float) containerHeight), this);
        final List<UnitValue> previousWidths = new ArrayList<>();
        for (final List<FlexItemInfo> line : lines) {
            for (final FlexItemInfo itemInfo : line) {
                final Rectangle rectangleWithoutBordersMarginsPaddings =
                        itemInfo.getRenderer().applyMarginsBordersPaddings(itemInfo.getRectangle().clone(), false);

                previousWidths.add(itemInfo.getRenderer().<UnitValue>getProperty(Property.WIDTH));

                itemInfo.getRenderer().setProperty(Property.WIDTH,
                        UnitValue.createPointValue(rectangleWithoutBordersMarginsPaddings.getWidth()));
                itemInfo.getRenderer().setProperty(Property.HEIGHT,
                        UnitValue.createPointValue(rectangleWithoutBordersMarginsPaddings.getHeight()));
            }
        }
        final LayoutResult result = super.layout(layoutContext);

        // We must set back widths of the children because multiple layouts are possible
        // If flex-grow is less than 1, layout algorithm increases the width of the element based on the initial width
        // And if we would not set back widths, every layout flex-item width will grow.
        int counter = 0;
        for (final List<FlexItemInfo> line : lines) {
            for (final FlexItemInfo itemInfo : line) {
                itemInfo.getRenderer().setProperty(Property.WIDTH, previousWidths.get(counter));
                ++counter;
            }
        }
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public MinMaxWidth getMinMaxWidth() {
        final MinMaxWidth minMaxWidth = new MinMaxWidth(calculateAdditionalWidth(this));
        final AbstractWidthHandler minMaxWidthHandler = new MaxMaxWidthHandler(minMaxWidth);
        if (!setMinMaxWidthBasedOnFixedWidth(minMaxWidth)) {
            final Float minWidth = hasAbsoluteUnitValue(Property.MIN_WIDTH) ? retrieveMinWidth(0) : null;
            final Float maxWidth = hasAbsoluteUnitValue(Property.MAX_WIDTH) ? retrieveMaxWidth(0) : null;
            if (minWidth == null || maxWidth == null) {
                findMinMaxWidthIfCorrespondingPropertiesAreNotSet(minMaxWidth, minMaxWidthHandler);
            }
            if (minWidth != null) {
                minMaxWidth.setChildrenMinWidth((float) minWidth);
            }
            // if max-width was defined explicitly, it shouldn't be overwritten
            if (maxWidth == null) {
                if (minMaxWidth.getChildrenMinWidth() > minMaxWidth.getChildrenMaxWidth()) {
                    minMaxWidth.setChildrenMaxWidth(minMaxWidth.getChildrenMinWidth());
                }
            } else {
                minMaxWidth.setChildrenMaxWidth((float) maxWidth);
            }
        }

        if (this.getPropertyAsFloat(Property.ROTATION_ANGLE) != null) {
            return RotationUtils.countRotationMinMaxWidth(minMaxWidth, this);
        }

        return minMaxWidth;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    AbstractRenderer[] createSplitAndOverflowRenderers(int childPos, int layoutStatus, LayoutResult childResult,
                                                       Map<Integer, IRenderer> waitingFloatsSplitRenderers,
                                                       List<IRenderer> waitingOverflowFloatRenderers) {
        final AbstractRenderer splitRenderer = createSplitRenderer(layoutStatus);
        final AbstractRenderer overflowRenderer = createOverflowRenderer(layoutStatus);
        final IRenderer childRenderer = childRenderers.get(childPos);
        final boolean forcedPlacement = Boolean.TRUE.equals(this.<Boolean>getProperty(Property.FORCED_PLACEMENT));
        boolean metChildRenderer = false;
        for (final List<FlexItemInfo> line : lines) {
            metChildRenderer = metChildRenderer ||
                    line.stream().anyMatch(flexItem -> flexItem.getRenderer() == childRenderer);
            for (final FlexItemInfo itemInfo : line) {
                if (metChildRenderer && !forcedPlacement) {
                    overflowRenderer.childRenderers.add(itemInfo.getRenderer());
                    itemInfo.getRenderer().setParent(overflowRenderer);
                } else {
                    splitRenderer.childRenderers.add(itemInfo.getRenderer());
                    itemInfo.getRenderer().setParent(splitRenderer);
                }
            }
        }

        overflowRenderer.deleteOwnProperty(Property.FORCED_PLACEMENT);

        return new AbstractRenderer[]{splitRenderer, overflowRenderer};
    }

    @Override
    LayoutResult processNotFullChildResult(LayoutContext layoutContext,
                                           Map<Integer, IRenderer> waitingFloatsSplitRenderers,
                                           List<IRenderer> waitingOverflowFloatRenderers, boolean wasHeightClipped,
                                           List<Rectangle> floatRendererAreas, boolean marginsCollapsingEnabled,
                                           float clearHeightCorrection, Border[] borders, UnitValue[] paddings,
                                           List<Rectangle> areas, int currentAreaPos, Rectangle layoutBox,
                                           Set<Rectangle> nonChildFloatingRendererAreas, IRenderer causeOfNothing,
                                           boolean anythingPlaced, int childPos, LayoutResult result) {

        final boolean keepTogether = isKeepTogether(causeOfNothing);

        final AbstractRenderer[] splitAndOverflowRenderers = createSplitAndOverflowRenderers(
                childPos, result.getStatus(), result, waitingFloatsSplitRenderers, waitingOverflowFloatRenderers);

        AbstractRenderer splitRenderer = splitAndOverflowRenderers[0];
        final AbstractRenderer overflowRenderer = splitAndOverflowRenderers[1];
        overflowRenderer.deleteOwnProperty(Property.FORCED_PLACEMENT);

        if (isRelativePosition() && !positionedRenderers.isEmpty()) {
            overflowRenderer.positionedRenderers = new ArrayList<>(positionedRenderers);
        }

        // TODO DEVSIX-5086 When flex-wrap will be fully supported we'll need to update height on split

        if (keepTogether) {
            splitRenderer = null;
            overflowRenderer.childRenderers.clear();
            overflowRenderer.childRenderers = new ArrayList<>(childRenderers);
        }

        correctFixedLayout(layoutBox);

        applyAbsolutePositionIfNeeded(layoutContext);

        if (Boolean.TRUE.equals(getPropertyAsBoolean(Property.FORCED_PLACEMENT)) || wasHeightClipped) {
            if (splitRenderer != null) {
                splitRenderer.childRenderers = new ArrayList<>(childRenderers);
                for (final IRenderer childRenderer : splitRenderer.childRenderers) {
                    childRenderer.setParent(splitRenderer);
                }
            }
            return new LayoutResult(LayoutResult.FULL, result.getOccupiedArea(), splitRenderer, null, null);
        } else {
            applyPaddings(occupiedArea.getBBox(), paddings, true);
            applyBorderBox(occupiedArea.getBBox(), borders, true);
            applyMargins(occupiedArea.getBBox(), true);
            if (splitRenderer == null || splitRenderer.childRenderers.isEmpty()) {
                return new LayoutResult(LayoutResult.NOTHING, null, null, overflowRenderer,
                        result.getCauseOfNothing()).setAreaBreak(result.getAreaBreak());
            } else {
                return new LayoutResult(LayoutResult.PARTIAL, layoutContext.getArea(), splitRenderer,
                        overflowRenderer, null).setAreaBreak(result.getAreaBreak());
            }
        }
    }

    @Override
    boolean stopLayoutingChildrenIfChildResultNotFull(LayoutResult returnResult) {
        return returnResult.getStatus() != LayoutResult.FULL;
    }

    @Override
    void decreaseLayoutBoxAfterChildPlacement(Rectangle layoutBox, LayoutResult result, IRenderer childRenderer) {
        // TODO DEVSIX-5086 When flex-wrap will be fully supported
        //  we'll need to decrease layout box with respect to the lines
        layoutBox.decreaseWidth(result.getOccupiedArea().getBBox().getWidth());
        layoutBox.moveRight(result.getOccupiedArea().getBBox().getWidth());
    }

    private void findMinMaxWidthIfCorrespondingPropertiesAreNotSet(MinMaxWidth minMaxWidth,
                                                                   AbstractWidthHandler minMaxWidthHandler) {
        // TODO DEVSIX-5086 When flex-wrap will be fully supported we'll find min/max width with respect to the lines
        for (final IRenderer childRenderer : childRenderers) {
            MinMaxWidth childMinMaxWidth;
            childRenderer.setParent(this);
            if (childRenderer instanceof AbstractRenderer) {
                childMinMaxWidth = ((AbstractRenderer) childRenderer).getMinMaxWidth();
            } else {
                childMinMaxWidth = MinMaxWidthUtils.countDefaultMinMaxWidth(childRenderer);
            }
            minMaxWidthHandler.updateMaxChildWidth(childMinMaxWidth.getMaxWidth() + minMaxWidth.getMaxWidth());
            minMaxWidthHandler.updateMinChildWidth(childMinMaxWidth.getMinWidth() + minMaxWidth.getMinWidth());
        }
    }

}