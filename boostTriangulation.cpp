// In this code a Delunay triangulation is created from a vector of sparse points.
// First a voronoi diagram is created using boost polygon. 
// After connections are created for every edge of the voronoi cell between cells sharing the same edge. 

#include <boost/polygon/voronoi.hpp>
#include <boost/polygon/point_data.hpp>
#include <boost/polygon/segment_data.hpp>

// Needed to check intersecting triangle edges when building the Delaunay triangulation from the Voronoi diagram
#include <boost/geometry/geometries/point_xy.hpp>
#include <boost/geometry/geometries/segment.hpp> 
#include <boost/geometry/algorithms/intersection.hpp>

using namespace boost::polygon;

// required to check intersection and collinearity
typedef boost::geometry::model::d2::point_xy<double> geometricPoint;
typedef boost::geometry::model::segment<geometricPoint> geometricSegment;

namespace triangulation
{
   typedef struct
   {
      // the triangle vertices
      int v0;
      int v1;
      int v2;
      // the indexes of the neighbouring triangles 
      int n0;
      int n1;
      int n2;
   } triangle;

   typedef struct
   {
      // the edge vertices
      int p0;
      int p1;
   } edge;

   const double eps = std::numeric_limits<double>::epsilon();

   inline bool operator== (const edge& lhs, const edge& rhs)
   {
      if (lhs.p0 == rhs.p0  &&  lhs.p1 == rhs.p1)
         return true;
      if (lhs.p0 == rhs.p1  &&  lhs.p1 == rhs.p0)
         return true;
      return false;
   }

   inline bool operator < (const edge& lhs, const edge& rhs)
   {
      // create two int array to be sorted
      std::vector<int> ev0, ev1;
      ev0.push_back(lhs.p0);
      ev0.push_back(lhs.p1);
      ev1.push_back(rhs.p0);
      ev1.push_back(rhs.p1);

      // sort the array 
      std::sort(ev0.begin(), ev0.end(), std::greater<int>());
      std::sort(ev1.begin(), ev1.end(), std::greater<int>());

      // strict weak ordering
      if (ev0[0] != ev1[0]) { return ev0[0] < ev1[0] ? true : false; }
      if (ev0[1] != ev1[1]) { return ev0[1] < ev1[1] ? true : false; }
      return false;
   }

   inline bool operator== (const triangle  lhs, const triangle  rhs)
   {
      // create two int array to be sorted
      std::vector<int> t0v, t1v;

      t0v.push_back(lhs.v0);
      t0v.push_back(lhs.v1);
      t0v.push_back(lhs.v2);

      t1v.push_back(rhs.v0);
      t1v.push_back(rhs.v1);
      t1v.push_back(rhs.v2);

      // sort the array 
      std::sort(t0v.begin(), t0v.end(), std::greater<int>());
      std::sort(t1v.begin(), t1v.end(), std::greater<int>());

      // compare the vertices
      if (t0v[0] != t1v[0]) return  false;
      if (t0v[1] != t1v[1]) return  false;
      if (t0v[2] != t1v[2]) return  false;

      return true;
   }

   // required to check intersection and collinearity
   typedef boost::geometry::model::d2::point_xy<double> geometricPoint;
   typedef boost::geometry::model::segment<geometricPoint> geometricSegment;

   // Loop over the voronoi cells and connect the centers of the cells sharing the same edge.
   // dTriang: the triangulation
   void triangulateFromVoronoi(const std::vector<point_data<double>> & points, std::vector<triangle>& dTriang, std::map<triangulation::edge, std::vector<size_t>> & gEdges)
   {
      voronoi_diagram<double> vd;
      construct_voronoi(points.begin(), points.end(), &vd);
      std::vector<const voronoi_edge<double>::voronoi_edge_type*> vtEdges(2);
      for (size_t ic = 0; ic != vd.cells().size(); ++ic)
      {
         if (vd.cells()[ic].contains_point())
         {
            int v0 = static_cast<int>(vd.cells()[ic].source_index());
            const voronoi_edge<double>* vedge = vd.cells()[ic].incident_edge();
            do
            {
               vedge = vedge->next();

               // Edges in CCW order
               vtEdges[0] = vedge;
               vtEdges[1] = vedge->next();
               // Do not build triangles just using points at the edges. We need at least one internal point to build a valid Delunay triangulation!
               if (vtEdges[0]->is_infinite() && vtEdges[1]->is_infinite()) continue;

               // Build new edges
               int v1 = static_cast<int>(vtEdges[0]->twin()->cell()->source_index());
               int v2 = static_cast<int>(vtEdges[1]->twin()->cell()->source_index());
               triangulation::edge e0, e1, e2;
               e0.p0 = v0;
               e0.p1 = v1;
               e1.p0 = v0;
               e1.p1 = v2;
               e2.p0 = v1;
               e2.p1 = v2;

               // Check the generated triangle is valid
               std::vector<triangulation::edge> lEdges(3);
               lEdges[0] = e0;
               lEdges[1] = e1;
               lEdges[2] = e2;
               bool invalidTriangle = false;
               std::vector<size_t> neighbouringTrianglesIndexses;
               for (int i = 0; i != 3; ++i)
               {
                  if (gEdges.count(lEdges[i]) != 0)
                  {
                     // the edge at the boundaries of the convex hull cannot be shared by more than one triangle. 
                     // skip this check for the last edge (a voronoi edge might be not defined in a degenerate case)
                     if (i < 2 && vtEdges[i]->is_infinite())
                     {
                        invalidTriangle = true;
                        break;
                     }
                     // internal edges cannot be shared by more than 2 triangles
                     if (gEdges[lEdges[i]].size() == 2)
                     {
                        invalidTriangle = true;
                        break;
                     }
                     // maximum one triangle is present at this point (the neighbour)
                     neighbouringTrianglesIndexses.push_back(gEdges[lEdges[i]].front());
                  }

                  // For the last oblique edge we must check 
                  // 1 . collinearity: if the edges are collinear than the triangles is degenerate
                  // 2 . is not intersecting other triangle edges (degenerate Voronoi vertex with degree > 3)
                  if (i == 2)
                  {
                     triangulation::geometricSegment obliqueSegment(triangulation::geometricPoint(points[v1].x(), points[v1].y()), triangulation::geometricPoint(points[v2].x(), points[v2].y()));
                     std::vector<geometricPoint> intersections;
                     double p0x = points[v0].x();
                     double p0y = points[v0].y();
                     double p1x = points[v1].x();
                     double p1y = points[v1].y();
                     triangulation::geometricSegment localSegment(triangulation::geometricPoint(p0x, p0y), triangulation::geometricPoint(p1x, p1y));
                     boost::geometry::intersection(obliqueSegment, localSegment, intersections);
                     // collinearity: a degenerated triangle 
                     if (intersections.size() == 2) invalidTriangle = true;

                     // need to check the oblique segment is not intersecting with another oblique segment
                     if (!neighbouringTrianglesIndexses.empty() && !invalidTriangle)
                     {
                        for (int nt = 0; nt != neighbouringTrianglesIndexses.size(); ++nt)
                        {
                           triangulation::triangle neighbouringTriangle = dTriang[neighbouringTrianglesIndexses[nt]];
                           p0x = points[neighbouringTriangle.v1].x();
                           p0y = points[neighbouringTriangle.v1].y();
                           p1x = points[neighbouringTriangle.v2].x();
                           p1y = points[neighbouringTriangle.v2].y();
                           triangulation::geometricSegment neighbouringObliqueSegment(triangulation::geometricPoint(p0x, p0y), triangulation::geometricPoint(p1x, p1y));
                           intersections.clear();
                           boost::geometry::intersection(obliqueSegment, neighbouringObliqueSegment, intersections);
                           if (intersections.size() == 1)
                           {
                              // it is valid if the intersection is only at one of the segment vertices
                              if ((intersections[0].x() == p0x &&  intersections[0].y() == p0y) || (intersections[0].x() == p1x &&  intersections[0].y() == p1y))
                              {
                                 continue;
                              }
                              else
                              {
                                 // it is invalid if the intersection is in the middle of another oblique edge 
                                 invalidTriangle = true;
                                 break;
                              }
                           }
                        }
                     }
                  }
               }
               if (invalidTriangle) continue;

               // The new triangle. The neighbouring triangles (n0, n1, n2) will be determined later
               triangulation::triangle t;
               t.n0 = -1;
               t.n1 = -1;
               t.n2 = -1;
               t.v0 = v0;
               t.v1 = v1;
               t.v2 = v2;
               if (std::find(dTriang.begin(), dTriang.end(), t) == dTriang.end())
               {
                  // add the new triangle to the gEdges map
                  for (int i = 0; i != 3; ++i)
                  {
                     gEdges[lEdges[i]].push_back(dTriang.size());
                  }
                  // add a new triangle
                  dTriang.push_back(t);
               }
            } while (vedge != vd.cells()[ic].incident_edge());
         }
      }


      // Determine the neighbouring triangles.
      for (size_t t = 0; t != dTriang.size(); ++t)
      {
         triangulation::edge e0, e1, e2;
         e0.p0 = dTriang[t].v0;
         e0.p1 = dTriang[t].v1;
         e1.p0 = dTriang[t].v1;
         e1.p1 = dTriang[t].v2;
         e2.p0 = dTriang[t].v2;
         e2.p1 = dTriang[t].v0;

         if (gEdges[e0].size() == 2) { dTriang[t].n2 = static_cast<int>(gEdges[e0].front() != t ? gEdges[e0].front() : gEdges[e0].back()); }
         if (gEdges[e1].size() == 2) { dTriang[t].n0 = static_cast<int>(gEdges[e1].front() != t ? gEdges[e1].front() : gEdges[e1].back()); }
         if (gEdges[e2].size() == 2) { dTriang[t].n1 = static_cast<int>(gEdges[e2].front() != t ? gEdges[e2].front() : gEdges[e2].back()); }
      }
   }
}