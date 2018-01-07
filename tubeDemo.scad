include <sweep.scad>
include <scad-utils/transformations.scad>
include <scad-utils/shapes.scad>

// Creates a tube sweeping an annular ring with continuous varying shape

npts   = 50;
// spiral path
path   = [for(a=[0:220/npts:220]) [30*cos(a), 30*sin(a), a/5]];
ptrans = construct_transform_path(path);
shape  = circle(20,$fn=20);

// additional shape transforms varying along the path
outer_shape_trans = [for(i=[0:npts]) rotation([0,0,3*i])*scaling([(0.5+0.7*i/npts), i/npts + 0.35*(1-i/npts), 1])];
inner_shape_trans = [for(i=[0:npts]) outer_shape_trans[i]*scaling([0.8,0.8,1])];
  
// combine ptrans with the shape transforms
outer_pstrans = [for(i=[0:len(ptrans)-1]) ptrans[i]*outer_shape_trans[i]];
inner_pstrans = [for(i=[0:len(ptrans)-1]) ptrans[i]*inner_shape_trans[i]];
  
// outer and inner sweep skins
outer_skin = sweep_polyhedron(shape, outer_pstrans, caps=false);
inner_skin = sweep_polyhedron(shape, inner_pstrans, caps=false, inv=true);

// annular end caps
outer_ends = [ transform(outer_pstrans[0], shape),
               transform(outer_pstrans[len(ptrans)-1], shape) ];
inner_ends = [ transform(inner_pstrans[0], shape),
               transform(inner_pstrans[len(ptrans)-1], shape) ];
beg_cap = annular_ring(outer_ends[0],inner_ends[0]);
end_cap = annular_ring(inner_ends[1],outer_ends[1]);

// all together
buildPolyhedron([outer_skin, inner_skin, beg_cap, end_cap]);


// Creates a polyhedron with the "union" of polyhedron data 
// ([points,faces]) found in the list polys
module buildPolyhedron(polys, convexity = 10) {
  function _accum_sum(l, res=[0]) =
    len(res) == len(l)+1 ?
      res :
      _accum_sum(l, concat(res, [ res[len(res)-1]+l[len(res)-1] ] ));

  vertlist = [for(p=polys, pt=p[0]) pt]; // collect all verts from all polyhedron data
  vertlen  = [for(p=polys) len(p[0]) ];  // vertex list size of each polyhedron data
  acclen   = _accum_sum(vertlen) ; // accumulated sum of vertex list size of each 
                                   // polyhedron data
  // collect all facets from all polyhedron data
  facets   = [ for(i=[0:len(polys)-1], f=polys[i][1] ) [ for(v=f) acclen[i]+v ] ];
  
  polyhedron(
    points = vertlist,
    faces  = facets,
    convexity = convexity
  );
}

// the polyhedron data of a annular ring connecting ring1 and ring2
// the order of the parameters defines the outer face of the ring
// the rings should be alligned to avoid twists
function annular_ring(ring1, ring2) =
  len(ring1)!=len(ring2) ? 
    echo("Rings should have same length") [[],[]] :
    let( verts = concat( ring1, ring2 ),
         n     = len(ring1),
         facet = [for(i=[0:n-1]) [i%n, (i+1)%n,   (i+1)%n+n, i+n ] ] )
    [ verts, facet ];

