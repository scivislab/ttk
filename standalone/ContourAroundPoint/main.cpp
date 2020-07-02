/// \author Christopher Kappe <kappe@cs.uni-kl.de>.
/// \date July 2, 2020.
///
/// \brief Standalone version of the `ContourAroundPoint` module.
// NOTE This is a bit of an effort to implement and thus sadly must wait;
// Currently it is just a copy of HelloWorld, with minimum changes to make it compile.

// TTK Includes
#include <CommandLineParser.h>
#include <ttkContourAroundPoint.h>

// VTK Includes
#include <vtkCellData.h>
#include <vtkDataArray.h>
#include <vtkDataSet.h>
#include <vtkPointData.h>
#include <vtkSmartPointer.h>
#include <vtkXMLDataObjectWriter.h>
#include <vtkXMLGenericDataObjectReader.h>

int main(int argc, char **argv) {

  // ---------------------------------------------------------------------------
  // Program variables
  // ---------------------------------------------------------------------------
  std::vector<std::string> inputFilePaths;
  std::vector<std::string> inputArrayNames;
  std::string outputArrayName{"AveragedArray"};
  std::string outputPathPrefix{"output"};
  bool listArrays{false};

  // ---------------------------------------------------------------------------
  // Set program variables based on command line arguments
  // ---------------------------------------------------------------------------
  {
    ttk::CommandLineParser parser;

    // -------------------------------------------------------------------------
    // Standard options and arguments
    // -------------------------------------------------------------------------
    parser.setArgument(
      "i", &inputFilePaths, "Input data-sets (*.vti, *vtu, *vtp)", false);
    parser.setArgument("a", &inputArrayNames, "Input array names", true);
    parser.setArgument(
      "o", &outputPathPrefix, "Output file prefix (no extension)", true);
    parser.setOption("l", &listArrays, "List available arrays");

    // -------------------------------------------------------------------------
    // TODO 1: Declare custom arguments and options
    // -------------------------------------------------------------------------
    parser.setArgument("O", &outputArrayName, "Output array name", true);

    parser.parse(argc, argv);
  }

  // ---------------------------------------------------------------------------
  // Command line output messages.
  // ---------------------------------------------------------------------------
  ttk::Debug msg;
  msg.setDebugMsgPrefix("ContourAroundPoint");

  // ---------------------------------------------------------------------------
  // Initialize ttkContourAroundPoint module (adjust parameters)
  // ---------------------------------------------------------------------------
  auto contourAroundPoint = vtkSmartPointer<ttkContourAroundPoint>::New();

  // ---------------------------------------------------------------------------
  // TODO 2: Pass custom arguments and options to the module
  // ---------------------------------------------------------------------------
  // contourAroundPoint->SetOutputArrayName(outputArrayName);

  // ---------------------------------------------------------------------------
  // Read input vtkDataObjects (optionally: print available arrays)
  // ---------------------------------------------------------------------------
  vtkDataArray *defaultArray = nullptr;
  for(size_t i = 0; i < inputFilePaths.size(); i++) {
    // init a reader that can parse any vtkDataObject stored in xml format
    auto reader = vtkSmartPointer<vtkXMLGenericDataObjectReader>::New();
    reader->SetFileName(inputFilePaths[i].data());
    reader->Update();

    // check if input vtkDataObject was successfully read
    auto inputDataObject = reader->GetOutput();
    if(!inputDataObject) {
      msg.printErr("Unable to read input file `" + inputFilePaths[i] + "' :(");
      return 0;
    }

    auto inputAsVtkDataSet = vtkDataSet::SafeDownCast(inputDataObject);

    // if requested print list of arrays, otherwise proceed with execution
    if(listArrays) {
      msg.printMsg(inputFilePaths[i] + ":");
      if(inputAsVtkDataSet) {
        // Point Data
        msg.printMsg("  PointData:");
        auto pointData = inputAsVtkDataSet->GetPointData();
        for(int j = 0; j < pointData->GetNumberOfArrays(); j++)
          msg.printMsg("    - " + std::string(pointData->GetArrayName(j)));

        // Cell Data
        msg.printMsg("  CellData:");
        auto cellData = inputAsVtkDataSet->GetCellData();
        for(int j = 0; j < cellData->GetNumberOfArrays(); j++)
          msg.printMsg("    - " + std::string(cellData->GetArrayName(j)));
      } else {
        msg.printErr("Unable to list arrays on file `" + inputFilePaths[i]
                     + "'");
        return 0;
      }
    } else {
      // feed input object to ttkHelloWorld filter
      contourAroundPoint->SetInputDataObject(i, reader->GetOutput());

      // default arrays
      if(!defaultArray) {
        defaultArray = inputAsVtkDataSet->GetPointData()->GetArray(0);
        if(!defaultArray)
          defaultArray = inputAsVtkDataSet->GetCellData()->GetArray(0);
      }
    }
  }

  // terminate program if it was just asked to list arrays
  if(listArrays) {
    return 1;
  }

  // ---------------------------------------------------------------------------
  // Specify which arrays of the input vtkDataObjects will be processed
  // ---------------------------------------------------------------------------
  if(!inputArrayNames.size()) {
    if(defaultArray)
      inputArrayNames.push_back(defaultArray->GetName());
  }
  for(size_t i = 0; i < inputArrayNames.size(); i++)
    contourAroundPoint->SetInputArrayToProcess(i, 0, 0, 0, inputArrayNames[i].data());

  // ---------------------------------------------------------------------------
  // Execute ttkHelloWorld filter
  // ---------------------------------------------------------------------------
  contourAroundPoint->Update();

  // ---------------------------------------------------------------------------
  // If output prefix is specified then write all output objects to disk
  // ---------------------------------------------------------------------------
  if(!outputPathPrefix.empty()) {
    for(int i = 0; i < contourAroundPoint->GetNumberOfOutputPorts(); i++) {
      auto output = contourAroundPoint->GetOutputDataObject(i);
      auto writer
        = vtkXMLDataObjectWriter::NewWriter(output->GetDataObjectType());

      std::string outputFileName = outputPathPrefix + "_port_"
                                   + std::to_string(i) + "."
                                   + writer->GetDefaultFileExtension();
      msg.printMsg("Writing output file `" + outputFileName + "'...");
      writer->SetInputDataObject(output);
      writer->SetFileName(outputFileName.data());
      writer->Update();
    }
  }

  return 1;
}
