/// \ingroup base
/// \class ttk::ConnectedComponents
/// \author Jonas Lukasczyk <jl@jluk.de>
/// \date 01.02.2019
///
/// \brief TTK %connectedComponents processing package.
///
/// This filter consumes a scalar field with a feature mask and computes for
/// each edge connected group of vertices with a non-background mask value a
/// so-called connected component via flood-filling, where the backgroud is
/// masked with values smaller-equal zero. The computed components store the
/// size, seed, and center of mass of each component. The flag
/// UseSeedIdAsComponentId controls if the resulting segmentation is either
/// labeled by the index of the component, or by its seed location (which can be
/// used as a deterministic component label).

#pragma once

// base code includes
#include <Debug.h>
#include <Triangulation.h>

#include <stack>

namespace ttk {
  class ConnectedComponents : virtual public Debug {

    using TID = ttk::SimplexId;

  private:
    static const int UNLABELED{-2};
    static const int IGNORE{-1};

  public:
    struct Component {
      int seed = -1;
      float center[3]{0, 0, 0};
      float size{0};
    };

    ConnectedComponents() {
      this->setDebugMsgPrefix("ConnectedComponents");
    };
    virtual ~ConnectedComponents() = default;

    int preconditionTriangulation(
      ttk::AbstractTriangulation *triangulation) const {
      return triangulation->preconditionVertexNeighbors();
    };

    template <typename TT = ttk::AbstractTriangulation>
    int computeFloodFill(int *labels,
                         std::vector<Component> &components,

                         const TT *triangulation,
                         const TID seed) const {
      // get component id
      const TID componentId = components.size();

      std::stack<TID> stack;
      stack.push(seed);
      labels[seed] = componentId;

      float size = 0;
      float x, y, z;
      float center[3] = {0, 0, 0};

      while(!stack.empty()) {
        const auto cIndex = stack.top();
        stack.pop();

        // update node data
        triangulation->getVertexPoint(cIndex, x, y, z);
        center[0] += x;
        center[1] += y;
        center[2] += z;
        size++;

        // add neihbors
        size_t nNeighbors = triangulation->getVertexNeighborNumber(cIndex);
        for(size_t i = 0; i < nNeighbors; i++) {
          TID nIndex;
          triangulation->getVertexNeighbor(cIndex, i, nIndex);
          if(labels[nIndex] == this->UNLABELED) {
            labels[nIndex] = componentId;
            stack.push(nIndex);
          }
        }
      }
      center[0] /= size;
      center[1] /= size;
      center[2] /= size;

      // create component
      components.resize(componentId + 1);
      auto &c = components[componentId];
      std::copy(center, center + 3, c.center);
      c.size = size;
      c.seed = seed;

      return 1;
    }

    template <typename DT>
    int initializeOutputLabels(int *labels,
                               const TID nVertices,
                               const DT *featureMask = nullptr) const {
      Timer timer;
      std::string msg
        = "Initializing IDs" + std::string(featureMask ? " via Mask" : "");
      this->printMsg(msg, 0, 0, 1, ttk::debug::LineMode::REPLACE);
      if(featureMask) {
        for(TID i = 0; i < nVertices; i++)
          labels[i] = featureMask[i] > 0 ? this->UNLABELED : this->IGNORE;
      } else {
        std::fill(labels, labels + nVertices, this->UNLABELED);
      }
      this->printMsg(msg, 1, timer.getElapsedTime(), 1);

      return 1;
    }

    template <typename TT = ttk::AbstractTriangulation>
    int computeConnectedComponents(std::vector<Component> &components,
                                   int *outputLabels,
                                   const TT *triangulation,
                                   const bool useSeedAsComponentId
                                   = false) const {

      TID nVertices = triangulation->getNumberOfVertices();

      {
        Timer timer;
        const std::string msg = "Computing Connected Components";
        this->printMsg(msg, 0, 0, 1, ttk::debug::LineMode::REPLACE);

        for(TID i = 0; i < nVertices; i++)
          if(outputLabels[i] == this->UNLABELED)
            this->computeFloodFill<TT>(
              outputLabels, components, triangulation, i);

        this->printMsg(msg, 1, timer.getElapsedTime(), 1);
      }

      if(useSeedAsComponentId) {
        Timer timer;
        const std::string msg = "Labeling Components by Seed Id";
        this->printMsg(msg, 0, 0, 1, ttk::debug::LineMode::REPLACE);

        for(TID i = 0; i < nVertices; i++) {
          auto &cid = outputLabels[i];
          if(cid >= 0)
            cid = components[cid].seed;
        }

        this->printMsg(msg, 1, timer.getElapsedTime(), 1);
      }

      return 1;
    }
  };
} // namespace ttk