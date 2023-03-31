# state file generated using paraview version 5.10.1

# uncomment the following three lines to ensure this script works in future versions
#import paraview
#paraview.compatibility.major = 5
#paraview.compatibility.minor = 10

#### import the simple module from the paraview
from paraview.simple import *
#### disable automatic camera reset on 'Show'
paraview.simple._DisableFirstRenderCameraReset()

# ----------------------------------------------------------------
# setup views used in the visualization
# ----------------------------------------------------------------

# get the material library
materialLibrary1 = GetMaterialLibrary()

# Create a new 'Render View'
renderView1 = CreateView('RenderView')
renderView1.ViewSize = [1617, 821]
renderView1.AxesGrid = 'GridAxes3DActor'
renderView1.OrientationAxesVisibility = 0
renderView1.CenterOfRotation = [0.4502498432993889, 0.12349999765865505, 0.02845747396349907]
renderView1.UseAmbientOcclusion = 1
renderView1.Background = [1.0, 1.0, 1.0]
renderView1.UseColorPaletteForBackground = 0
renderView1.StereoType = 'Crystal Eyes'
renderView1.CameraPosition = [0.43663628609238286, -0.44425971795351693, 0.6169323526164728]
renderView1.CameraFocalPoint = [0.4490484647025778, 0.11919295102463945, 0.024337075537263254]
renderView1.CameraViewUp = [0.002230222932606053, 0.7246767494127156, 0.6890853611609313]
renderView1.CameraFocalDisk = 1.0
renderView1.CameraParallelScale = 0.3749740097180616
renderView1.BackEnd = 'OSPRay raycaster'
renderView1.Backgroundmode = 'Backplate'
renderView1.EnvironmentalBG = [0.9975585564965286, 0.9975585564965286, 0.9975585564965286]
renderView1.OSPRayMaterialLibrary = materialLibrary1

# Create a new 'Render View'
renderView3 = CreateView('RenderView')
renderView3.ViewSize = [1617, 821]
renderView3.AxesGrid = 'GridAxes3DActor'
renderView3.OrientationAxesVisibility = 0
renderView3.Background = [1.0, 1.0, 1.0]
renderView3.UseColorPaletteForBackground = 0
renderView3.CenterOfRotation = [-0.44999921321868896, 0.8285380899906158, 0.0]
renderView3.StereoType = 'Crystal Eyes'
renderView3.CameraPosition = [1.8997641773149958, 5.425777318916059, 5.263079088762304]
renderView3.CameraFocalPoint = [0.016167227331822156, 0.5599002052918852, 0.08283180824519885]
renderView3.CameraViewUp = [-0.2172413348703541, 0.7496498926872297, -0.6251649708819038]
renderView3.CameraFocalDisk = 1.0
renderView3.CameraParallelScale = 1.2997569329883842
renderView3.CameraParallelProjection = 1
renderView3.BackEnd = 'OSPRay raycaster'
renderView3.Backgroundmode = 'Backplate'
renderView3.EnvironmentalBG = [0.9975585564965286, 0.9975585564965286, 0.9975585564965286]
renderView3.OSPRayMaterialLibrary = materialLibrary1

SetActiveView(None)

# ----------------------------------------------------------------
# setup view layouts
# ----------------------------------------------------------------

# create new layout object 'Layout #1'
layout1 = CreateLayout(name='Layout #1')
layout1.AssignView(0, renderView1)
layout1.SetSize(1800, 800)

# create new layout object 'Layout #3'
layout3 = CreateLayout(name='Layout #3')
layout3.AssignView(0, renderView3)
layout3.SetSize(1800, 800)

# ----------------------------------------------------------------
# restore active view
SetActiveView(renderView1)
# ----------------------------------------------------------------

# ----------------------------------------------------------------
# setup the data processing pipelines
# ----------------------------------------------------------------

# create a new 'XML Image Data Reader'
multifield0126zslicetxtdensityvti = XMLImageDataReader(registrationName='multifield.0126.zslice.txt.density.vti', FileName=['data/multifield.0126.zslice.txt.density.vti'])
multifield0126zslicetxtdensityvti.CellArrayStatus = ['vtkGhostType']
multifield0126zslicetxtdensityvti.PointArrayStatus = ['density', 'vtkValidPointMask', 'vtkGhostType']
multifield0126zslicetxtdensityvti.TimeArray = 'None'

# create a new 'XML Image Data Reader'
multifield0127zslicetxtdensityvti = XMLImageDataReader(registrationName='multifield.0127.zslice.txt.density.vti', FileName=['data/multifield.0127.zslice.txt.density.vti'])
multifield0127zslicetxtdensityvti.CellArrayStatus = ['vtkGhostType']
multifield0127zslicetxtdensityvti.PointArrayStatus = ['density', 'vtkValidPointMask', 'vtkGhostType']
multifield0127zslicetxtdensityvti.TimeArray = 'None'

# create a new 'TTK BlockAggregator'
tTKBlockAggregator1 = TTKBlockAggregator(registrationName='TTKBlockAggregator1', Input=[multifield0126zslicetxtdensityvti, multifield0127zslicetxtdensityvti])

# create a new 'Clip'
clip1 = Clip(registrationName='Clip1', Input=tTKBlockAggregator1)
clip1.ClipType = 'Plane'
clip1.HyperTreeGridClipper = 'Plane'
clip1.Scalars = ['POINTS', 'density']
clip1.Value = 0.5000009768371569

# init the 'Plane' selected for 'ClipType'
clip1.ClipType.Origin = [0.2995, 0.12349999999999998, 1.23500000004384e-07]
clip1.ClipType.Normal = [-1.0, 0.0, 0.0]

# init the 'Plane' selected for 'HyperTreeGridClipper'
clip1.HyperTreeGridClipper.Origin = [0.2995, 0.12349999999999998, 1.23500000004384e-07]

# create a new 'Tetrahedralize'
tetrahedralize1 = Tetrahedralize(registrationName='Tetrahedralize1', Input=clip1)

# create a new 'Extract Block'
extractBlock2 = ExtractBlock(registrationName='ExtractBlock2', Input=tetrahedralize1)
extractBlock2.Selectors = ['/Root']

# create a new 'Warp By Scalar'
warpByScalar1 = WarpByScalar(registrationName='WarpByScalar1', Input=extractBlock2)
warpByScalar1.Scalars = ['POINTS', 'density']
warpByScalar1.ScaleFactor = 0.05091494974922606

# create a new 'TTK TopologicalSimplificationByPersistence'
tTKTopologicalSimplificationByPersistence2 = TTKTopologicalSimplificationByPersistence(registrationName='TTKTopologicalSimplificationByPersistence2', Input=warpByScalar1)
tTKTopologicalSimplificationByPersistence2.InputArray = ['POINTS', 'density']
tTKTopologicalSimplificationByPersistence2.PersistenceThreshold = 0.05
tTKTopologicalSimplificationByPersistence2.NumericalPerturbation = 1

# create a new 'TTK Merge and Contour Tree (FTM)'
tTKMergeandContourTreeFTM1 = TTKMergeandContourTreeFTM(registrationName='TTKMergeandContourTreeFTM1', Input=tTKTopologicalSimplificationByPersistence2)
tTKMergeandContourTreeFTM1.ScalarField = ['POINTS', 'density']
tTKMergeandContourTreeFTM1.InputOffsetField = ['POINTS', 'density']
tTKMergeandContourTreeFTM1.TreeType = 'Split Tree'
tTKMergeandContourTreeFTM1.UseAllCores = 0

# find source
tTKMergeandContourTreeFTM1_1 = FindSource('TTKMergeandContourTreeFTM1')

# find source
tTKMergeandContourTreeFTM1_2 = FindSource('TTKMergeandContourTreeFTM1')

# create a new 'TTK BlockAggregator'
tTKBlockAggregator2 = TTKBlockAggregator(registrationName='TTKBlockAggregator2', Input=[tTKMergeandContourTreeFTM1, OutputPort(tTKMergeandContourTreeFTM1_1,1), OutputPort(tTKMergeandContourTreeFTM1_2,2)])
tTKBlockAggregator2.FlattenInput = 0

# create a new 'TTK MergeTreeClustering'
tTKMergeTreeClustering2 = TTKMergeTreeClustering(registrationName='TTKMergeTreeClustering2', Input=tTKBlockAggregator2,
    OptionalInputclustering=None)
tTKMergeTreeClustering2.ComputeBarycenter = 1
tTKMergeTreeClustering2.DimensionSpacing = 0.5
tTKMergeTreeClustering2.DimensionToshift = 'Custom'
tTKMergeTreeClustering2.ZShift = 1.0
tTKMergeTreeClustering2.Barycenterpositionaccordingtoalpha = 1
tTKMergeTreeClustering2.OutputSegmentation = 1
tTKMergeTreeClustering2.Epsilon1 = 0.0
tTKMergeTreeClustering2.Epsilon2 = 100.0
tTKMergeTreeClustering2.Epsilon3 = 100.0
tTKMergeTreeClustering2.PathPlanarLayout = 1
tTKMergeTreeClustering2.ImportantPairs = 39.0
tTKMergeTreeClustering2.ImportantPairsSpacing = 0.3
tTKMergeTreeClustering2.NonImportantPairsSpacing = 5.0
tTKMergeTreeClustering2.NonImportantPairsProximity = 0.015

# find source
tTKMergeTreeClustering2_1 = FindSource('TTKMergeTreeClustering2')

# create a new 'TTK BlockAggregator'
tTKBlockAggregator3 = TTKBlockAggregator(registrationName='TTKBlockAggregator3', Input=[tTKMergeTreeClustering2, OutputPort(tTKMergeTreeClustering2_1,1)])
tTKBlockAggregator3.FlattenInput = 0

# create a new 'Extract Block'
extractBlock4 = ExtractBlock(registrationName='ExtractBlock4', Input=tTKBlockAggregator3)
extractBlock4.Selectors = ['/Root/Block0/Block1', '/Root/Block1/Block1']

# create a new 'Threshold'
threshold11 = Threshold(registrationName='Threshold11', Input=extractBlock4)
threshold11.Scalars = ['CELLS', 'isImportantPair']

# create a new 'Extract Surface'
extractSurface3 = ExtractSurface(registrationName='ExtractSurface3', Input=threshold11)

# create a new 'Tube'
tube3 = Tube(registrationName='Tube3', Input=extractSurface3)
tube3.Scalars = ['POINTS', 'Scalar']
tube3.Vectors = ['POINTS', '1']
tube3.Radius = 0.005

# create a new 'Threshold'
threshold10 = Threshold(registrationName='Threshold10', Input=extractBlock4)
threshold10.Scalars = ['CELLS', 'isImportantPair']
threshold10.LowerThreshold = 1.0
threshold10.UpperThreshold = 1.0

# create a new 'Extract Surface'
extractSurface4 = ExtractSurface(registrationName='ExtractSurface4', Input=threshold10)

# create a new 'Tube'
tube4 = Tube(registrationName='Tube4', Input=extractSurface4)
tube4.Scalars = ['POINTS', 'Scalar']
tube4.Vectors = ['POINTS', '1']
tube4.Radius = 0.007

# find source
tTKMergeTreeClustering2_2 = FindSource('TTKMergeTreeClustering2')

# create a new 'Threshold'
threshold5 = Threshold(registrationName='Threshold5', Input=OutputPort(tTKMergeTreeClustering2_2,2))
threshold5.Scalars = ['CELLS', 'MatchingType']
threshold5.LowerThreshold = 2.0
threshold5.UpperThreshold = 2.0

# create a new 'Threshold'
threshold16 = Threshold(registrationName='Threshold16', Input=threshold5)
threshold16.Scalars = ['CELLS', 'MatchingPercentMatch']
threshold16.LowerThreshold = 200.0
threshold16.UpperThreshold = 200.0

# create a new 'Threshold'
threshold6 = Threshold(registrationName='Threshold6', Input=threshold16)
threshold6.Scalars = ['CELLS', 'MeanMatchedPersistence']
threshold6.LowerThreshold = 0.15
threshold6.UpperThreshold = 0.9999999403953552

# create a new 'TTK IdentifyByScalarField'
tTKIdentifyByScalarField3 = TTKIdentifyByScalarField(registrationName='TTKIdentifyByScalarField3', Input=threshold6)
tTKIdentifyByScalarField3.ScalarField = ['CELLS', 'mergeTree1NodeId']

# create a new 'Extract Surface'
extractSurface2 = ExtractSurface(registrationName='ExtractSurface2', Input=tTKIdentifyByScalarField3)

# create a new 'Tube'
tube2 = Tube(registrationName='Tube2', Input=extractSurface2)
tube2.Scalars = ['POINTS', '']
tube2.Vectors = ['POINTS', '1']
tube2.Radius = 0.008

# create a new 'Cell Data to Point Data'
cellDatatoPointData2 = CellDatatoPointData(registrationName='CellDatatoPointData2', Input=tTKIdentifyByScalarField3)
cellDatatoPointData2.CellDataArraytoprocess = ['Cost', 'MatchingID', 'MatchingPercentMatch', 'MatchingType', 'MeanMatchedPersistence', 'mergeTree1NodeId', 'mergeTree2NodeId', 'tree1NodeId', 'tree2NodeId']

# create a new 'TTK IcospheresFromPoints'
tTKIcospheresFromPoints5 = TTKIcospheresFromPoints(registrationName='TTKIcospheresFromPoints5', Input=cellDatatoPointData2)
tTKIcospheresFromPoints5.Radius = 0.03

# create a new 'TTK MergeTreeClustering'
tTKMergeTreeClustering1 = TTKMergeTreeClustering(registrationName='TTKMergeTreeClustering1', Input=tTKBlockAggregator2,
    OptionalInputclustering=None)
tTKMergeTreeClustering1.ComputeBarycenter = 1
tTKMergeTreeClustering1.Deterministic = 1
tTKMergeTreeClustering1.DimensionSpacing = 0.1
tTKMergeTreeClustering1.Barycenterpositionaccordingtoalpha = 1
tTKMergeTreeClustering1.PlanarLayout = 0
tTKMergeTreeClustering1.OutputSegmentation = 1
tTKMergeTreeClustering1.Epsilon1 = 0.0
tTKMergeTreeClustering1.Epsilon2 = 100.0
tTKMergeTreeClustering1.Epsilon3 = 100.0
tTKMergeTreeClustering1.ImportantPairs = 45.0

# create a new 'Extract Block'
extractBlock1 = ExtractBlock(registrationName='ExtractBlock1', Input=tTKMergeTreeClustering1)
extractBlock1.Selectors = ['/Root/Block2']

# find source
tTKMergeTreeClustering1_1 = FindSource('TTKMergeTreeClustering1')

# create a new 'Threshold'
threshold17 = Threshold(registrationName='Threshold17', Input=OutputPort(tTKMergeTreeClustering1_1,2))
threshold17.Scalars = ['CELLS', 'MatchingPercentMatch']
threshold17.LowerThreshold = 200.0
threshold17.UpperThreshold = 200.0

# create a new 'Threshold'
threshold2 = Threshold(registrationName='Threshold2', Input=threshold17)
threshold2.Scalars = ['CELLS', 'MatchingType']
threshold2.LowerThreshold = 2.0
threshold2.UpperThreshold = 2.0

# create a new 'Threshold'
threshold8 = Threshold(registrationName='Threshold8', Input=threshold2)
threshold8.Scalars = ['CELLS', 'MeanMatchedPersistence']
threshold8.LowerThreshold = 0.15
threshold8.UpperThreshold = 0.9999999403953552

# create a new 'TTK IdentifyByScalarField'
tTKIdentifyByScalarField2 = TTKIdentifyByScalarField(registrationName='TTKIdentifyByScalarField2', Input=threshold8)
tTKIdentifyByScalarField2.ScalarField = ['CELLS', 'mergeTree1NodeId']

# create a new 'Extract Surface'
extractSurface1 = ExtractSurface(registrationName='ExtractSurface1', Input=tTKIdentifyByScalarField2)

# create a new 'Tube'
tube1 = Tube(registrationName='Tube1', Input=extractSurface1)
tube1.Scalars = ['POINTS', '']
tube1.Vectors = ['POINTS', '1']
tube1.Radius = 0.003

# create a new 'Cell Data to Point Data'
cellDatatoPointData1 = CellDatatoPointData(registrationName='CellDatatoPointData1', Input=tTKIdentifyByScalarField2)
cellDatatoPointData1.CellDataArraytoprocess = ['CellScalarFieldName', 'Cost', 'MatchingID', 'MatchingPercentMatch', 'MatchingType', 'MeanMatchedPersistence', 'mergeTree1NodeId', 'mergeTree2NodeId', 'tree1NodeId', 'tree2NodeId']

# create a new 'Threshold'
threshold1 = Threshold(registrationName='Threshold1', Input=threshold2)
threshold1.Scalars = ['CELLS', 'MeanMatchedPersistence']
threshold1.UpperThreshold = 0.15

# create a new 'Extract Surface'
extractSurface5 = ExtractSurface(registrationName='ExtractSurface5', Input=threshold1)

# create a new 'Tube'
tube5 = Tube(registrationName='Tube5', Input=extractSurface5)
tube5.Scalars = ['POINTS', 'isBarycenterNode']
tube5.Vectors = ['POINTS', '1']
tube5.Radius = 0.001

# create a new 'Mask Points'
maskPoints3 = MaskPoints(registrationName='MaskPoints3', Input=threshold1)
maskPoints3.OnRatio = 0
maskPoints3.GenerateVertices = 1
maskPoints3.SingleVertexPerCell = 1

# create a new 'Threshold'
threshold9 = Threshold(registrationName='Threshold9', Input=maskPoints3)
threshold9.Scalars = ['POINTS', 'isBarycenterNode']

# create a new 'TTK IcospheresFromPoints'
tTKIcospheresFromPoints3 = TTKIcospheresFromPoints(registrationName='TTKIcospheresFromPoints3', Input=threshold9)
tTKIcospheresFromPoints3.Radius = 0.005

# create a new 'Mask Points'
maskPoints1 = MaskPoints(registrationName='MaskPoints1', Input=cellDatatoPointData1)
maskPoints1.OnRatio = 0
maskPoints1.GenerateVertices = 1
maskPoints1.SingleVertexPerCell = 1

# create a new 'Threshold'
threshold7 = Threshold(registrationName='Threshold7', Input=maskPoints1)
threshold7.Scalars = ['POINTS', 'isBarycenterNode']

# create a new 'TTK IcospheresFromPoints'
tTKIcospheresFromPoints2 = TTKIcospheresFromPoints(registrationName='TTKIcospheresFromPoints2', Input=threshold7)
tTKIcospheresFromPoints2.Radius = 0.008

# create a new 'Extract Block'
extractBlock3 = ExtractBlock(registrationName='ExtractBlock3', Input=tTKBlockAggregator3)
extractBlock3.Selectors = ['/Root/Block0/Block0', '/Root/Block1/Block0']

# create a new 'Mask Points'
maskPoints2 = MaskPoints(registrationName='MaskPoints2', Input=extractBlock3)
maskPoints2.OnRatio = 0
maskPoints2.GenerateVertices = 1
maskPoints2.SingleVertexPerCell = 1

# create a new 'Threshold'
threshold3 = Threshold(registrationName='Threshold3', Input=maskPoints2)
threshold3.Scalars = ['POINTS', 'isDummyNode']
threshold3.LowerThreshold = 1.0
threshold3.UpperThreshold = 1.0

# create a new 'TTK IcospheresFromPoints'
tTKIcospheresFromPoints4 = TTKIcospheresFromPoints(registrationName='TTKIcospheresFromPoints4', Input=threshold3)
tTKIcospheresFromPoints4.Radius = 0.005

# create a new 'Threshold'
threshold15 = Threshold(registrationName='Threshold15', Input=tTKIcospheresFromPoints4)
threshold15.Scalars = ['POINTS', 'isImportantPair']
threshold15.LowerThreshold = 1.0
threshold15.UpperThreshold = 1.0

# create a new 'Threshold'
threshold4 = Threshold(registrationName='Threshold4', Input=maskPoints2)
threshold4.Scalars = ['POINTS', 'isDummyNode']

# create a new 'TTK IcospheresFromPoints'
tTKIcospheresFromPoints1 = TTKIcospheresFromPoints(registrationName='TTKIcospheresFromPoints1', Input=threshold4)
tTKIcospheresFromPoints1.Radius = 0.015

# create a new 'Threshold'
threshold14 = Threshold(registrationName='Threshold14', Input=tTKIcospheresFromPoints1)
threshold14.Scalars = ['POINTS', 'isImportantPair']
threshold14.LowerThreshold = 1.0
threshold14.UpperThreshold = 1.0

# create a new 'Threshold'
threshold12 = Threshold(registrationName='Threshold12', Input=tTKIcospheresFromPoints1)
threshold12.Scalars = ['POINTS', 'isImportantPair']

# create a new 'Threshold'
threshold13 = Threshold(registrationName='Threshold13', Input=threshold12)
threshold13.Scalars = ['POINTS', 'CriticalType']
threshold13.LowerThreshold = 3.0
threshold13.UpperThreshold = 3.0

# ----------------------------------------------------------------
# setup the visualization in view 'renderView1'
# ----------------------------------------------------------------

# show data from extractBlock1
extractBlock1Display = Show(extractBlock1, renderView1, 'UnstructuredGridRepresentation')

# get color transfer function/color map for 'density'
densityLUT = GetColorTransferFunction('density')
densityLUT.RGBPoints = [9.999999974752427e-07, 0.82, 0.98, 0.96, 0.25, 0.3, 0.9, 0.9, 0.5000009768371569, 0.3, 0.35, 0.35, 0.75, 0.3, 0.6, 0.9, 1.0000009536743164, 0.6, 0.75, 0.98]
densityLUT.ColorSpace = 'Lab'
densityLUT.ScalarRangeInitialized = 1.0

# get opacity transfer function/opacity map for 'density'
densityPWF = GetOpacityTransferFunction('density')
densityPWF.Points = [9.999999974752427e-07, 0.0, 0.5, 0.0, 1.0000009536743164, 1.0, 0.5, 0.0, 1.0000009536743164, 0.0, 0.5, 0.0]
densityPWF.ScalarRangeInitialized = 1

# trace defaults for the display properties.
extractBlock1Display.Representation = 'Surface'
extractBlock1Display.AmbientColor = [0.0, 0.0, 0.0]
extractBlock1Display.ColorArrayName = ['POINTS', 'density']
extractBlock1Display.LookupTable = densityLUT
extractBlock1Display.Specular = 0.85
extractBlock1Display.Diffuse = 0.9
extractBlock1Display.SelectTCoordArray = 'None'
extractBlock1Display.SelectNormalArray = 'None'
extractBlock1Display.SelectTangentArray = 'None'
extractBlock1Display.OSPRayScaleArray = 'SegmentationId'
extractBlock1Display.OSPRayScaleFunction = 'PiecewiseFunction'
extractBlock1Display.SelectOrientationVectors = 'None'
extractBlock1Display.ScaleFactor = 0.06994996815919877
extractBlock1Display.SelectScaleArray = 'SegmentationId'
extractBlock1Display.GlyphType = 'Arrow'
extractBlock1Display.GlyphTableIndexArray = 'SegmentationId'
extractBlock1Display.GaussianRadius = 0.0034974984079599383
extractBlock1Display.SetScaleArray = ['POINTS', 'SegmentationId']
extractBlock1Display.ScaleTransferFunction = 'PiecewiseFunction'
extractBlock1Display.OpacityArray = ['POINTS', 'SegmentationId']
extractBlock1Display.OpacityTransferFunction = 'PiecewiseFunction'
extractBlock1Display.DataAxesGrid = 'GridAxesRepresentation'
extractBlock1Display.PolarAxes = 'PolarAxesRepresentation'
extractBlock1Display.ScalarOpacityFunction = densityPWF
extractBlock1Display.ScalarOpacityUnitDistance = 0.011152296139841634
extractBlock1Display.OpacityArrayName = ['POINTS', 'SegmentationId']

# init the 'GridAxesRepresentation' selected for 'DataAxesGrid'
extractBlock1Display.DataAxesGrid.XTitleColor = [0.0, 0.0, 0.0]
extractBlock1Display.DataAxesGrid.YTitleColor = [0.0, 0.0, 0.0]
extractBlock1Display.DataAxesGrid.ZTitleColor = [0.0, 0.0, 0.0]
extractBlock1Display.DataAxesGrid.GridColor = [0.0, 0.0, 0.0]
extractBlock1Display.DataAxesGrid.XLabelColor = [0.0, 0.0, 0.0]
extractBlock1Display.DataAxesGrid.YLabelColor = [0.0, 0.0, 0.0]
extractBlock1Display.DataAxesGrid.ZLabelColor = [0.0, 0.0, 0.0]

# init the 'PolarAxesRepresentation' selected for 'PolarAxes'
extractBlock1Display.PolarAxes.PolarAxisTitleColor = [0.0, 0.0, 0.0]
extractBlock1Display.PolarAxes.PolarAxisLabelColor = [0.0, 0.0, 0.0]
extractBlock1Display.PolarAxes.LastRadialAxisTextColor = [0.0, 0.0, 0.0]
extractBlock1Display.PolarAxes.SecondaryRadialAxesTextColor = [0.0, 0.0, 0.0]

# show data from tube1
tube1Display = Show(tube1, renderView1, 'GeometryRepresentation')

# get color transfer function/color map for 'CellScalarFieldName'
cellScalarFieldNameLUT = GetColorTransferFunction('CellScalarFieldName')
cellScalarFieldNameLUT.RGBPoints = [0.0, 0.82, 0.98, 0.96, 0.9999960463255082, 0.3, 0.9, 0.9, 2.0, 0.3, 0.35, 0.35, 2.9999961389768743, 0.3, 0.6, 0.9, 4.0, 0.6, 0.75, 0.98]
cellScalarFieldNameLUT.ColorSpace = 'Lab'
cellScalarFieldNameLUT.ScalarRangeInitialized = 1.0

# trace defaults for the display properties.
tube1Display.Representation = 'Surface'
tube1Display.ColorArrayName = ['CELLS', 'CellScalarFieldName']
tube1Display.LookupTable = cellScalarFieldNameLUT
tube1Display.Specular = 1.0
tube1Display.SelectTCoordArray = 'None'
tube1Display.SelectNormalArray = 'TubeNormals'
tube1Display.SelectTangentArray = 'None'
tube1Display.OSPRayScaleArray = 'TubeNormals'
tube1Display.OSPRayScaleFunction = 'PiecewiseFunction'
tube1Display.SelectOrientationVectors = 'None'
tube1Display.ScaleFactor = 0.05283976942300797
tube1Display.SelectScaleArray = 'None'
tube1Display.GlyphType = 'Arrow'
tube1Display.GlyphTableIndexArray = 'None'
tube1Display.GaussianRadius = 0.0026419884711503983
tube1Display.SetScaleArray = ['POINTS', 'TubeNormals']
tube1Display.ScaleTransferFunction = 'PiecewiseFunction'
tube1Display.OpacityArray = ['POINTS', 'TubeNormals']
tube1Display.OpacityTransferFunction = 'PiecewiseFunction'
tube1Display.DataAxesGrid = 'GridAxesRepresentation'
tube1Display.PolarAxes = 'PolarAxesRepresentation'

# init the 'PiecewiseFunction' selected for 'ScaleTransferFunction'
tube1Display.ScaleTransferFunction.Points = [-0.9781877994537354, 0.0, 0.5, 0.0, 0.9781877994537354, 1.0, 0.5, 0.0]

# init the 'PiecewiseFunction' selected for 'OpacityTransferFunction'
tube1Display.OpacityTransferFunction.Points = [-0.9781877994537354, 0.0, 0.5, 0.0, 0.9781877994537354, 1.0, 0.5, 0.0]

# show data from tTKIcospheresFromPoints2
tTKIcospheresFromPoints2Display = Show(tTKIcospheresFromPoints2, renderView1, 'GeometryRepresentation')

# trace defaults for the display properties.
tTKIcospheresFromPoints2Display.Representation = 'Surface'
tTKIcospheresFromPoints2Display.ColorArrayName = ['POINTS', 'CellScalarFieldName']
tTKIcospheresFromPoints2Display.LookupTable = cellScalarFieldNameLUT
tTKIcospheresFromPoints2Display.Specular = 1.0
tTKIcospheresFromPoints2Display.SelectTCoordArray = 'None'
tTKIcospheresFromPoints2Display.SelectNormalArray = 'Normals'
tTKIcospheresFromPoints2Display.SelectTangentArray = 'None'
tTKIcospheresFromPoints2Display.OSPRayScaleArray = 'CellScalarFieldName'
tTKIcospheresFromPoints2Display.OSPRayScaleFunction = 'PiecewiseFunction'
tTKIcospheresFromPoints2Display.SelectOrientationVectors = 'None'
tTKIcospheresFromPoints2Display.ScaleFactor = 0.06219998151063919
tTKIcospheresFromPoints2Display.SelectScaleArray = 'CellScalarFieldName'
tTKIcospheresFromPoints2Display.GlyphType = 'Arrow'
tTKIcospheresFromPoints2Display.GlyphTableIndexArray = 'CellScalarFieldName'
tTKIcospheresFromPoints2Display.GaussianRadius = 0.0031099990755319596
tTKIcospheresFromPoints2Display.SetScaleArray = ['POINTS', 'CellScalarFieldName']
tTKIcospheresFromPoints2Display.ScaleTransferFunction = 'PiecewiseFunction'
tTKIcospheresFromPoints2Display.OpacityArray = ['POINTS', 'CellScalarFieldName']
tTKIcospheresFromPoints2Display.OpacityTransferFunction = 'PiecewiseFunction'
tTKIcospheresFromPoints2Display.DataAxesGrid = 'GridAxesRepresentation'
tTKIcospheresFromPoints2Display.PolarAxes = 'PolarAxesRepresentation'

# init the 'PiecewiseFunction' selected for 'ScaleTransferFunction'
tTKIcospheresFromPoints2Display.ScaleTransferFunction.Points = [0.0, 0.0, 0.5, 0.0, 4.0, 1.0, 0.5, 0.0]

# init the 'PiecewiseFunction' selected for 'OpacityTransferFunction'
tTKIcospheresFromPoints2Display.OpacityTransferFunction.Points = [0.0, 0.0, 0.5, 0.0, 4.0, 1.0, 0.5, 0.0]

# show data from tTKIcospheresFromPoints3
tTKIcospheresFromPoints3Display = Show(tTKIcospheresFromPoints3, renderView1, 'GeometryRepresentation')

# trace defaults for the display properties.
tTKIcospheresFromPoints3Display.Representation = 'Surface'
tTKIcospheresFromPoints3Display.AmbientColor = [0.8627450980392157, 0.8627450980392157, 0.8627450980392157]
tTKIcospheresFromPoints3Display.ColorArrayName = ['POINTS', '']
tTKIcospheresFromPoints3Display.DiffuseColor = [0.8627450980392157, 0.8627450980392157, 0.8627450980392157]
tTKIcospheresFromPoints3Display.Specular = 1.0
tTKIcospheresFromPoints3Display.SelectTCoordArray = 'None'
tTKIcospheresFromPoints3Display.SelectNormalArray = 'Normals'
tTKIcospheresFromPoints3Display.SelectTangentArray = 'None'
tTKIcospheresFromPoints3Display.OSPRayScaleArray = 'Normals'
tTKIcospheresFromPoints3Display.OSPRayScaleFunction = 'PiecewiseFunction'
tTKIcospheresFromPoints3Display.SelectOrientationVectors = 'None'
tTKIcospheresFromPoints3Display.ScaleFactor = 0.05739998072385788
tTKIcospheresFromPoints3Display.SelectScaleArray = 'None'
tTKIcospheresFromPoints3Display.GlyphType = 'Arrow'
tTKIcospheresFromPoints3Display.GlyphTableIndexArray = 'None'
tTKIcospheresFromPoints3Display.GaussianRadius = 0.002869999036192894
tTKIcospheresFromPoints3Display.SetScaleArray = ['POINTS', 'Normals']
tTKIcospheresFromPoints3Display.ScaleTransferFunction = 'PiecewiseFunction'
tTKIcospheresFromPoints3Display.OpacityArray = ['POINTS', 'Normals']
tTKIcospheresFromPoints3Display.OpacityTransferFunction = 'PiecewiseFunction'
tTKIcospheresFromPoints3Display.DataAxesGrid = 'GridAxesRepresentation'
tTKIcospheresFromPoints3Display.PolarAxes = 'PolarAxesRepresentation'

# init the 'PiecewiseFunction' selected for 'ScaleTransferFunction'
tTKIcospheresFromPoints3Display.ScaleTransferFunction.Points = [-1.0, 0.0, 0.5, 0.0, 1.0, 1.0, 0.5, 0.0]

# init the 'PiecewiseFunction' selected for 'OpacityTransferFunction'
tTKIcospheresFromPoints3Display.OpacityTransferFunction.Points = [-1.0, 0.0, 0.5, 0.0, 1.0, 1.0, 0.5, 0.0]

# show data from tube5
tube5Display = Show(tube5, renderView1, 'GeometryRepresentation')

# trace defaults for the display properties.
tube5Display.Representation = 'Surface'
tube5Display.AmbientColor = [0.8627450980392157, 0.8627450980392157, 0.8627450980392157]
tube5Display.ColorArrayName = ['POINTS', '']
tube5Display.DiffuseColor = [0.8627450980392157, 0.8627450980392157, 0.8627450980392157]
tube5Display.Specular = 0.5
tube5Display.SelectTCoordArray = 'None'
tube5Display.SelectNormalArray = 'TubeNormals'
tube5Display.SelectTangentArray = 'None'
tube5Display.OSPRayScaleArray = 'TubeNormals'
tube5Display.OSPRayScaleFunction = 'PiecewiseFunction'
tube5Display.SelectOrientationVectors = 'None'
tube5Display.ScaleFactor = 0.05647456496953965
tube5Display.SelectScaleArray = 'None'
tube5Display.GlyphType = 'Arrow'
tube5Display.GlyphTableIndexArray = 'None'
tube5Display.GaussianRadius = 0.0028237282484769822
tube5Display.SetScaleArray = ['POINTS', 'TubeNormals']
tube5Display.ScaleTransferFunction = 'PiecewiseFunction'
tube5Display.OpacityArray = ['POINTS', 'TubeNormals']
tube5Display.OpacityTransferFunction = 'PiecewiseFunction'
tube5Display.DataAxesGrid = 'GridAxesRepresentation'
tube5Display.PolarAxes = 'PolarAxesRepresentation'

# init the 'PiecewiseFunction' selected for 'ScaleTransferFunction'
tube5Display.ScaleTransferFunction.Points = [-0.9436343908309937, 0.0, 0.5, 0.0, 0.9436343908309937, 1.0, 0.5, 0.0]

# init the 'PiecewiseFunction' selected for 'OpacityTransferFunction'
tube5Display.OpacityTransferFunction.Points = [-0.9436343908309937, 0.0, 0.5, 0.0, 0.9436343908309937, 1.0, 0.5, 0.0]

# ----------------------------------------------------------------
# setup the visualization in view 'renderView3'
# ----------------------------------------------------------------

# show data from tube2
tube2Display = Show(tube2, renderView3, 'GeometryRepresentation')

# trace defaults for the display properties.
tube2Display.Representation = 'Surface'
tube2Display.ColorArrayName = ['CELLS', 'CellScalarFieldName']
tube2Display.LookupTable = cellScalarFieldNameLUT
tube2Display.Specular = 1.0
tube2Display.SelectTCoordArray = 'None'
tube2Display.SelectNormalArray = 'TubeNormals'
tube2Display.SelectTangentArray = 'None'
tube2Display.OSPRayScaleArray = 'TubeNormals'
tube2Display.OSPRayScaleFunction = 'PiecewiseFunction'
tube2Display.SelectOrientationVectors = 'None'
tube2Display.ScaleFactor = 0.31114061754196887
tube2Display.SelectScaleArray = 'None'
tube2Display.GlyphType = 'Arrow'
tube2Display.GlyphTableIndexArray = 'None'
tube2Display.GaussianRadius = 0.015557030877098442
tube2Display.SetScaleArray = ['POINTS', 'TubeNormals']
tube2Display.ScaleTransferFunction = 'PiecewiseFunction'
tube2Display.OpacityArray = ['POINTS', 'TubeNormals']
tube2Display.OpacityTransferFunction = 'PiecewiseFunction'
tube2Display.DataAxesGrid = 'GridAxesRepresentation'
tube2Display.PolarAxes = 'PolarAxesRepresentation'

# init the 'PiecewiseFunction' selected for 'ScaleTransferFunction'
tube2Display.ScaleTransferFunction.Points = [-1.0, 0.0, 0.5, 0.0, 1.0, 1.0, 0.5, 0.0]

# init the 'PiecewiseFunction' selected for 'OpacityTransferFunction'
tube2Display.OpacityTransferFunction.Points = [-1.0, 0.0, 0.5, 0.0, 1.0, 1.0, 0.5, 0.0]

# show data from tube3
tube3Display = Show(tube3, renderView3, 'GeometryRepresentation')

# trace defaults for the display properties.
tube3Display.Representation = 'Surface'
tube3Display.AmbientColor = [0.8627450980392157, 0.8627450980392157, 0.8627450980392157]
tube3Display.ColorArrayName = ['POINTS', '']
tube3Display.DiffuseColor = [0.8627450980392157, 0.8627450980392157, 0.8627450980392157]
tube3Display.Specular = 1.0
tube3Display.SelectTCoordArray = 'None'
tube3Display.SelectNormalArray = 'TubeNormals'
tube3Display.SelectTangentArray = 'None'
tube3Display.OSPRayScaleArray = 'Scalar'
tube3Display.OSPRayScaleFunction = 'PiecewiseFunction'
tube3Display.SelectOrientationVectors = 'None'
tube3Display.ScaleFactor = 0.3112929729744792
tube3Display.SelectScaleArray = 'None'
tube3Display.GlyphType = 'Arrow'
tube3Display.GlyphTableIndexArray = 'None'
tube3Display.GaussianRadius = 0.01556464864872396
tube3Display.SetScaleArray = ['POINTS', 'Scalar']
tube3Display.ScaleTransferFunction = 'PiecewiseFunction'
tube3Display.OpacityArray = ['POINTS', 'Scalar']
tube3Display.OpacityTransferFunction = 'PiecewiseFunction'
tube3Display.DataAxesGrid = 'GridAxesRepresentation'
tube3Display.PolarAxes = 'PolarAxesRepresentation'

# init the 'PiecewiseFunction' selected for 'ScaleTransferFunction'
tube3Display.ScaleTransferFunction.Points = [9.999999974752427e-07, 0.0, 0.5, 0.0, 1.0000009536743164, 1.0, 0.5, 0.0]

# init the 'PiecewiseFunction' selected for 'OpacityTransferFunction'
tube3Display.OpacityTransferFunction.Points = [9.999999974752427e-07, 0.0, 0.5, 0.0, 1.0000009536743164, 1.0, 0.5, 0.0]

# show data from tTKIcospheresFromPoints5
tTKIcospheresFromPoints5Display = Show(tTKIcospheresFromPoints5, renderView3, 'GeometryRepresentation')

# trace defaults for the display properties.
tTKIcospheresFromPoints5Display.Representation = 'Surface'
tTKIcospheresFromPoints5Display.ColorArrayName = ['POINTS', 'CellScalarFieldName']
tTKIcospheresFromPoints5Display.LookupTable = cellScalarFieldNameLUT
tTKIcospheresFromPoints5Display.Specular = 1.0
tTKIcospheresFromPoints5Display.SelectTCoordArray = 'None'
tTKIcospheresFromPoints5Display.SelectNormalArray = 'Normals'
tTKIcospheresFromPoints5Display.SelectTangentArray = 'None'
tTKIcospheresFromPoints5Display.OSPRayScaleArray = 'Cost'
tTKIcospheresFromPoints5Display.OSPRayScaleFunction = 'PiecewiseFunction'
tTKIcospheresFromPoints5Display.SelectOrientationVectors = 'None'
tTKIcospheresFromPoints5Display.ScaleFactor = 0.20399999618530273
tTKIcospheresFromPoints5Display.SelectScaleArray = 'Cost'
tTKIcospheresFromPoints5Display.GlyphType = 'Arrow'
tTKIcospheresFromPoints5Display.GlyphTableIndexArray = 'Cost'
tTKIcospheresFromPoints5Display.GaussianRadius = 0.010199999809265137
tTKIcospheresFromPoints5Display.SetScaleArray = ['POINTS', 'Cost']
tTKIcospheresFromPoints5Display.ScaleTransferFunction = 'PiecewiseFunction'
tTKIcospheresFromPoints5Display.OpacityArray = ['POINTS', 'Cost']
tTKIcospheresFromPoints5Display.OpacityTransferFunction = 'PiecewiseFunction'
tTKIcospheresFromPoints5Display.DataAxesGrid = 'GridAxesRepresentation'
tTKIcospheresFromPoints5Display.PolarAxes = 'PolarAxesRepresentation'

# init the 'PiecewiseFunction' selected for 'ScaleTransferFunction'
tTKIcospheresFromPoints5Display.ScaleTransferFunction.Points = [0.0, 0.0, 0.5, 0.0, 1.1757813367477812e-38, 1.0, 0.5, 0.0]

# init the 'PiecewiseFunction' selected for 'OpacityTransferFunction'
tTKIcospheresFromPoints5Display.OpacityTransferFunction.Points = [0.0, 0.0, 0.5, 0.0, 1.1757813367477812e-38, 1.0, 0.5, 0.0]

# show data from threshold13
threshold13Display = Show(threshold13, renderView3, 'UnstructuredGridRepresentation')

# trace defaults for the display properties.
threshold13Display.Representation = 'Surface'
threshold13Display.AmbientColor = [0.8627450980392157, 0.8627450980392157, 0.8627450980392157]
threshold13Display.ColorArrayName = ['POINTS', '']
threshold13Display.DiffuseColor = [0.8627450980392157, 0.8627450980392157, 0.8627450980392157]
threshold13Display.Specular = 1.0
threshold13Display.SelectTCoordArray = 'None'
threshold13Display.SelectNormalArray = 'Normals'
threshold13Display.SelectTangentArray = 'None'
threshold13Display.OSPRayScaleArray = 'BranchBaryNodeID'
threshold13Display.OSPRayScaleFunction = 'PiecewiseFunction'
threshold13Display.SelectOrientationVectors = 'None'
threshold13Display.ScaleFactor = 0.3147933006286621
threshold13Display.SelectScaleArray = 'BranchBaryNodeID'
threshold13Display.GlyphType = 'Arrow'
threshold13Display.GlyphTableIndexArray = 'BranchBaryNodeID'
threshold13Display.GaussianRadius = 0.015739665031433106
threshold13Display.SetScaleArray = ['POINTS', 'BranchBaryNodeID']
threshold13Display.ScaleTransferFunction = 'PiecewiseFunction'
threshold13Display.OpacityArray = ['POINTS', 'BranchBaryNodeID']
threshold13Display.OpacityTransferFunction = 'PiecewiseFunction'
threshold13Display.DataAxesGrid = 'GridAxesRepresentation'
threshold13Display.PolarAxes = 'PolarAxesRepresentation'
threshold13Display.ScalarOpacityUnitDistance = 0.13401275883414793
threshold13Display.OpacityArrayName = ['POINTS', 'BranchBaryNodeID']

# init the 'PiecewiseFunction' selected for 'ScaleTransferFunction'
threshold13Display.ScaleTransferFunction.Points = [2.0, 0.0, 0.5, 0.0, 29.0, 1.0, 0.5, 0.0]

# init the 'PiecewiseFunction' selected for 'OpacityTransferFunction'
threshold13Display.OpacityTransferFunction.Points = [2.0, 0.0, 0.5, 0.0, 29.0, 1.0, 0.5, 0.0]

# show data from threshold14
threshold14Display = Show(threshold14, renderView3, 'UnstructuredGridRepresentation')

# get color transfer function/color map for 'Scalar'
scalarLUT = GetColorTransferFunction('Scalar')
scalarLUT.RGBPoints = [9.999999974752427e-07, 0.82, 0.98, 0.96, 0.25, 0.3, 0.9, 0.9, 0.5000009768371569, 0.3, 0.35, 0.35, 0.75, 0.3, 0.6, 0.9, 1.0000009536743164, 0.6, 0.75, 0.98]
scalarLUT.ColorSpace = 'Lab'
scalarLUT.ScalarRangeInitialized = 1.0

# get opacity transfer function/opacity map for 'Scalar'
scalarPWF = GetOpacityTransferFunction('Scalar')
scalarPWF.Points = [9.999999974752427e-07, 0.0, 0.5, 0.0, 1.0000009536743164, 1.0, 0.5, 0.0, 1.0000009536743164, 0.0, 0.5, 0.0]
scalarPWF.ScalarRangeInitialized = 1

# trace defaults for the display properties.
threshold14Display.Representation = 'Surface'
threshold14Display.ColorArrayName = ['POINTS', 'Scalar']
threshold14Display.LookupTable = scalarLUT
threshold14Display.Specular = 1.0
threshold14Display.SelectTCoordArray = 'None'
threshold14Display.SelectNormalArray = 'Normals'
threshold14Display.SelectTangentArray = 'None'
threshold14Display.OSPRayScaleArray = 'BranchBaryNodeID'
threshold14Display.OSPRayScaleFunction = 'PiecewiseFunction'
threshold14Display.SelectOrientationVectors = 'None'
threshold14Display.ScaleFactor = 0.3224000215530396
threshold14Display.SelectScaleArray = 'BranchBaryNodeID'
threshold14Display.GlyphType = 'Arrow'
threshold14Display.GlyphTableIndexArray = 'BranchBaryNodeID'
threshold14Display.GaussianRadius = 0.016120001077651977
threshold14Display.SetScaleArray = ['POINTS', 'BranchBaryNodeID']
threshold14Display.ScaleTransferFunction = 'PiecewiseFunction'
threshold14Display.OpacityArray = ['POINTS', 'BranchBaryNodeID']
threshold14Display.OpacityTransferFunction = 'PiecewiseFunction'
threshold14Display.DataAxesGrid = 'GridAxesRepresentation'
threshold14Display.PolarAxes = 'PolarAxesRepresentation'
threshold14Display.ScalarOpacityFunction = scalarPWF
threshold14Display.ScalarOpacityUnitDistance = 0.1854779920338356
threshold14Display.OpacityArrayName = ['POINTS', 'BranchBaryNodeID']

# init the 'PiecewiseFunction' selected for 'ScaleTransferFunction'
threshold14Display.ScaleTransferFunction.Points = [0.0, 0.0, 0.5, 0.0, 24.0, 1.0, 0.5, 0.0]

# init the 'PiecewiseFunction' selected for 'OpacityTransferFunction'
threshold14Display.OpacityTransferFunction.Points = [0.0, 0.0, 0.5, 0.0, 24.0, 1.0, 0.5, 0.0]

# show data from threshold15
threshold15Display = Show(threshold15, renderView3, 'UnstructuredGridRepresentation')

# trace defaults for the display properties.
threshold15Display.Representation = 'Surface'
threshold15Display.ColorArrayName = ['POINTS', 'Scalar']
threshold15Display.LookupTable = scalarLUT
threshold15Display.Specular = 1.0
threshold15Display.SelectTCoordArray = 'None'
threshold15Display.SelectNormalArray = 'Normals'
threshold15Display.SelectTangentArray = 'None'
threshold15Display.OSPRayScaleArray = 'BranchBaryNodeID'
threshold15Display.OSPRayScaleFunction = 'PiecewiseFunction'
threshold15Display.SelectOrientationVectors = 'None'
threshold15Display.ScaleFactor = 0.3210000276565552
threshold15Display.SelectScaleArray = 'BranchBaryNodeID'
threshold15Display.GlyphType = 'Arrow'
threshold15Display.GlyphTableIndexArray = 'BranchBaryNodeID'
threshold15Display.GaussianRadius = 0.01605000138282776
threshold15Display.SetScaleArray = ['POINTS', 'BranchBaryNodeID']
threshold15Display.ScaleTransferFunction = 'PiecewiseFunction'
threshold15Display.OpacityArray = ['POINTS', 'BranchBaryNodeID']
threshold15Display.OpacityTransferFunction = 'PiecewiseFunction'
threshold15Display.DataAxesGrid = 'GridAxesRepresentation'
threshold15Display.PolarAxes = 'PolarAxesRepresentation'
threshold15Display.ScalarOpacityFunction = scalarPWF
threshold15Display.ScalarOpacityUnitDistance = 0.19353873864065005
threshold15Display.OpacityArrayName = ['POINTS', 'BranchBaryNodeID']

# init the 'PiecewiseFunction' selected for 'ScaleTransferFunction'
threshold15Display.ScaleTransferFunction.Points = [0.0, 0.0, 0.5, 0.0, 24.0, 1.0, 0.5, 0.0]

# init the 'PiecewiseFunction' selected for 'OpacityTransferFunction'
threshold15Display.OpacityTransferFunction.Points = [0.0, 0.0, 0.5, 0.0, 24.0, 1.0, 0.5, 0.0]

# show data from tube4
tube4Display = Show(tube4, renderView3, 'GeometryRepresentation')

# trace defaults for the display properties.
tube4Display.Representation = 'Surface'
tube4Display.ColorArrayName = ['POINTS', 'Scalar']
tube4Display.LookupTable = scalarLUT
tube4Display.Specular = 1.0
tube4Display.SelectTCoordArray = 'None'
tube4Display.SelectNormalArray = 'TubeNormals'
tube4Display.SelectTangentArray = 'None'
tube4Display.OSPRayScaleArray = 'Scalar'
tube4Display.OSPRayScaleFunction = 'PiecewiseFunction'
tube4Display.SelectOrientationVectors = 'None'
tube4Display.ScaleFactor = 0.3210000276565552
tube4Display.SelectScaleArray = 'None'
tube4Display.GlyphType = 'Arrow'
tube4Display.GlyphTableIndexArray = 'None'
tube4Display.GaussianRadius = 0.01605000138282776
tube4Display.SetScaleArray = ['POINTS', 'Scalar']
tube4Display.ScaleTransferFunction = 'PiecewiseFunction'
tube4Display.OpacityArray = ['POINTS', 'Scalar']
tube4Display.OpacityTransferFunction = 'PiecewiseFunction'
tube4Display.DataAxesGrid = 'GridAxesRepresentation'
tube4Display.PolarAxes = 'PolarAxesRepresentation'

# init the 'PiecewiseFunction' selected for 'ScaleTransferFunction'
tube4Display.ScaleTransferFunction.Points = [9.999999974752427e-07, 0.0, 0.5, 0.0, 1.0000009536743164, 1.0, 0.5, 0.0]

# init the 'PiecewiseFunction' selected for 'OpacityTransferFunction'
tube4Display.OpacityTransferFunction.Points = [9.999999974752427e-07, 0.0, 0.5, 0.0, 1.0000009536743164, 1.0, 0.5, 0.0]

# ----------------------------------------------------------------
# setup color maps and opacity mapes used in the visualization
# note: the Get..() functions create a new object, if needed
# ----------------------------------------------------------------

# get opacity transfer function/opacity map for 'CellScalarFieldName'
cellScalarFieldNamePWF = GetOpacityTransferFunction('CellScalarFieldName')
cellScalarFieldNamePWF.Points = [0.0, 0.0, 0.5, 0.0, 4.0, 1.0, 0.5, 0.0, 4.0, 0.0, 0.5, 0.0]
cellScalarFieldNamePWF.ScalarRangeInitialized = 1

# ----------------------------------------------------------------
# restore active source
SetActiveSource(None)
# ----------------------------------------------------------------


SaveScreenshot("output/teaser-wasserstein-terrain.png", layout1)
SaveScreenshot("output/teaser-wasserstein-trees.png",   layout3)