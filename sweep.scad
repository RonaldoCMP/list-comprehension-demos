use <scad-utils/linalg.scad>
use <scad-utils/transformations.scad>

//////////////////////////////////////////////////////////////////////////////////
//
//  This library is strongly based on the Oskar Linde's library sweep.scad found in
//
//      https://github.com/openscad/list-comprehension-demos
//
//  Note that it requires some libraries from scad-utils which can be found in
//
//      https://github.com/OskarLinde/scad-utils
//
//  My work on it was:
//      1. incorporate the minimum twist code Oskar Linde posted in the Openscad Forum 
//         (http://forum.openscad.org/Twisty-problem-with-scad-utils-quot-sweep-quot-tc9775.html)
//      2. polishing some functions (simplifying some, allowing tail-recursion eliminination, etc)
//      3. include comments
//      4. add three helper functions to allow the control of sweep twists:
//              - adjusted_rotations(path_transf, angini=0, angtot=0, closed=false)
//              - adjusted_directions(path_transf, v0, vf=undef, turns=0, closed=false)
//              - referenced_path_transforms(path, vref, closed)
//      5. include the possibility to the user computation of the path tangents
//
//  The last function is a substitute to the original construct_transform_path(path, closed=false)
//  It is useful to constraint the sweep rotations to keep the sections aligned with a surface normal.
//  See the SweepDemo.scad for examples of usage.
//
//      Ronaldo Persiano
//
//////////////////////////////////////////////////////////////////////////////////////////
//
//  API functions
//  =============
//
//  Although some other functions may have their application to user codes, the main API function are:
//
//  module sweep(shape, path_transforms, closed=false)
//  --------------------------------------------------
//  It builds a polyhedron representing the sweep of of a 2D shape along a path implicit in the
//  path_transforms sequence. This sequence is computed by other functions in the library or coded
//  by users. This module arguments are:
//
//      shape           - a list of 2d vertices of a simple polygon
//      path_transforms -   a sequence of rigid body transforms (4x4 matrices)
//      closed          - true if the path of the path_transforms is closed
//
//  function sweep_polyhedron(shape, path_transforms, closed=false)
//  ---------------------------------------------------------------
//  The function applies each transform path_transforms[i] to the shape and builds an 
//  envelope to the transformed shapes. If closed==true, connects the last to the 
//  first one. Otherwise, builds a cap at each end of the envelope. The resulting envelope 
//  data is returned as a polyhedron primitive input data [ points, faces ].
//  This function is called by module sweep(). It has, however, its own value in 
//  non-linear deformation of sweeping models. The function arguments are:
//
//      shape           - a list of 2d vertices of a simple polygon
//      path_transforms -   a sequence of rigid body transforms.
//      closed      - true if the path of the path_transforms is closed
//      caps        - either a boolean or a list of two booleans
//                    caps=[b1,b2] -> a cap is added at the begining (end) of the path 
//                                    if and only if b1 (b2) is true
//                    caps=true    -> equivalent to [true,true]; it is the default
//                    caps=false   -> equivalent to [false,false]
//                    caps is ignored if closed=true
//      inv         - the orientation of all faces are reverted if inv=true; deffault false
//
//  It is called by module sweep.
//
//  function construct_transform_path(path, closed=false, tangts)
//  ------------------------------------------------------------
//  Construct a list of rigid body transforms mapping the 3D origin to points of the path.
//  This is the fundamental base for the sweeping method which maps a section by the 
//  transforms and builds their envelope. If the argument tangts is given, this list
//  of the tangent at each point of path is taken instead of the internal computed sequence.
//  Returns a path transform list to feed sweep().
//
//  function adjusted_rotations(path_transf, angini=0, angtot=0, closed=false) 
//  --------------------------------------------------------------------------
//  Given an already built path transforms 'path_transf', this function adds (or subtract) 
//  an additional twist of value 'angtot' to each path_transf after rotating the initial section 
//  by 'angini'. If both angini and angtot are zero, the path_transf is unchanged.
//  Returns the resulting a new path transform list to feed sweep().
//
//  function adjusted_directions(path_transf, v0, vf=undef, turns=0, closed=false)
//  ------------------------------------------------------------------------------
//  Given an already built path transforms 'path_transf', this function adjust it in such a 
//  way that the x-axis of the section is mapped to the direction nearest to v0 
//  at the path start and to the direction nearest to vf at the path end. 
//  Additional twist turns (360 degrees twist) may be added or subtracted. 
//  Returns the resulting path transform list.
//
//  function referenced_path_transforms(path, vref, closed=false, tangts)
//  ---------------------------------------------------------------------
//  This function is an alternative to construct_transform_path. 
//  Given a path and a vector vref[i] for each point path[i],  the function computes 
//  a path transform list for sweeping such that the y-axis of the section is mapped 
//  to the vector vref[i] at point path[i]. The normal to the mapped section plane
//  is taken as the vector orthogonal to vref[i] nearest to the tangent of the path
//  at point path[i]. If the argument tangts is given, this list of the tangent at each
//  point of path is taken instead of tangent_path(path).
//  Returns the resulting path transform list.
//
//  module sweep_sections(shape, path_transforms)
//  ---------------------------------------------
//  This module has only debugging purposes. It draws just the 2d sections at the positions
//  of the path that are mapped by sweep.
//  
//  See SweepDemo.scad for usage.
//
//////////////////////////////////////////////////////////////////////////////////////////

function unit(v) = norm(v)>0 ? v/norm(v) : undef; 

function transpose(m) = // m is any retangular matrix of objects
  [ for(j=[0:len(m[0])-1]) [ for(i=[0:len(m)-1]) m[i][j] ] ];

function identity(n) = [for(i=[0:n-1]) [for(j=[0:n-1]) i==j ? 1 : 0] ];

// computes the rotation with minimum angle that brings a to b
function rotate_from_to(a,b) = 
    let( axis = unit(cross(a,b)) )
    axis*axis >= 0.99 ? 
        transpose([unit(b), axis, cross(axis, unit(b))]) * 
            [unit(a), axis, cross(axis, unit(a))] : 
        identity(3); 

// computes the sequence of minimizing rotations that brings one tangent to the next one.
function minimizing_rotations(tangents) = 
    [ for (i = [0:len(tangents)-2])
        rotate_from_to(tangents[i],tangents[i+1])
    ];

// generates the sequence of all partial compositions (matrix multiplication) of rots[j] 
// from 0 to i
function accumulate_rotations(rots) = 
    _acc_rots(rots, [ rots[0] ]);
    
function _acc_rots(rots, acc_) = 
    len(acc_) == len(rots) ? 
        acc_ :
        _acc_rots(rots, concat(acc_, [ rots[len(acc_)] * acc_[len(acc_)-1] ]));

// computes the sequence of path unitary tangents to the given path. 
// If closed==true, assumes the path is closed.
function tangent_path(path, closed) =
    let( l = len(path) )
    closed ?
        [ for(i=[0:l-1]) unit(path[(i+1)%l]-path[(l+i-1)%l]) ] :
        concat( [ unit(path[1] - path[0]) ], 
                [ for(i=[1:l-2]) unit(path[i+1]-path[i-1]) ],
                [ unit(path[l-1] - path[l-2]) ]
              );

// This function is not used anywhere here. 
// Computes an alternative sequence of path unitary tangents to the given path. 
// If closed==true, assumes the path is closed.
function tangents(spine, closed=false) = 
    let( n = len(spine) )
    closed?
        [ for(i=[0:n-1]) unit(spine[(n+i-2)%n] - 8*spine[(n+i-1)%n] + 8*spine[(i+1)%n] - spine[(i+2)%n]) ] :
        concat(
          [ unit(-25*spine[0] +48*spine[1] -36*spine[2] +16*spine[3] -3*spine[4]),
            unit(- 3*spine[0] -10*spine[1] +18*spine[2] - 6*spine[3] +  spine[4]) ]
             ,
          [ for(i=[2:n-3]) unit(spine[i-2] - 8*spine[i-1] + 8*spine[i+1] - spine[i+2]) ]
             ,
          [ unit( 3*spine[n-1] +10*spine[n-2] -18*spine[n-3] + 6*spine[n-4] -  spine[n-5]),
            unit(25*spine[n-1] -48*spine[n-2] +36*spine[n-3] -16*spine[n-4] +3*spine[n-5]) ]
         );

// builds the compositions of rotations r[i] and translation t[i] in 4x4 matrices
function construct_rt(r,t) = 
    [ concat(r[0], t[0]), concat(r[1],t[1]), concat(r[2], t[2]), [0,0,0,1] ];

// Given two rotations A and B, calculates the angle between B*[1,0,0] 
// and A*[1,0,0] that is, the total torsion angle difference between A and B.
function calculate_twist(A,B) = 
    let( D = transpose(B) * A)  
    atan2(D[1][0], D[0][0]); 

function construct_transform_path(path, closed=false, tangts) = 
   let( l = len(path),
        tangents = tangts==undef ? tangent_path(path, closed) : tangts,
        local_rotations = minimizing_rotations(concat([[0,0,1]], tangents)),
        rotations = accumulate_rotations(local_rotations),
        twist = closed ? calculate_twist(rotations[0], rotations[l-1]) : 0 )
   [ for (i = [0:l-1]) construct_rt(rotations[i], path[i]) * rotation( [0, 0, twist*i/(l-1)] ) ];

function adjusted_rotations(path_transf, angini=0, angtot=0, closed=false) = 
     let( l    = len(path_transf),
          atot = closed ? 360*floor(angtot/360)/(l-1) : angtot/(l-1) )
     [ for(i=[0:l-1]) path_transf[i]*rotation([0,0,atot*i+angini]) ];

function adjusted_directions(path_transf, v0, vf=undef, turns=0, closed=false) = 
     let( vp0  = [v0[0],v0[1],v0[2],0]*path_transf[0],
          ang0 = atan2(vp0[1], vp0[0]),
          vpf  = [vf[0],vf[1],vf[2],0]*path_transf[len(path_transf)-1],
          twst = vf == undef ? 0 : atan2(vpf[1], vpf[0]) - ang0,
          angf = turns*360 + twst )
     adjusted_rotations(path_transf, angini=ang0, angtot=angf, closed=closed);

function referenced_path_transforms(path, vref, closed=false, tangts) =
    let( l     = len(path),
         tgts  = tangts==undef ? tangent_path(path, closed) : tangts,
         vunit = [ for(v=vref) unit(v) ],
         // project tgts[i] in the plane orthogonal to vref[i]
         tgtr  = [ for(i=[0:l-1]) tgts[i]-(tgts[i]*vunit[i])*vunit[i] ],
         // builds the frame 
         rots  = [ for(i=[0:l-1]) 
                    let( vcross = unit(cross(tgtr[i], vunit[i])) )
                    vcross != undef ?
                        transpose([ vcross, vunit[i], tgtr[i] ]):
                        identity(3) 
                ] )
    [ for (i = [0:l-1]) construct_rt(rots[i], path[i]) ];

function sweep_polyhedron(shape, path_transforms, closed=false, caps=true, inv=false) = 
    let(    pathlen  = len(path_transforms),
            segments = pathlen + (closed ? 0 : -1),
            shape3d  = to_3d(shape),
            sweep_points =
                [ for ( i=[0:pathlen-1], pts = transform(path_transforms[i], shape3d) ) pts ],
            loop_faces = let (facets = len(shape3d))
                            [ for( s=[0:segments-1], i=[0:facets-1] )
                                let( s0 = (s%pathlen)*facets,
                                     s1 = ((s+1)%pathlen) * facets )
                                inv ?
                                    [ s0 + i, s1 + i, s1 + (i+1)%facets, s0 + (i+1)%facets ] :
                                    [ s0 + i, s0 + (i+1)%facets, s1 + (i+1)%facets, s1 + i ]     
                            ],
            bcap = closed || !caps || !caps[0],
            ecap = closed || !caps || !caps[1],
            rng1 = inv ? [0:len(shape3d)-1] : [len(shape3d)-1:-1:0],
            rng2 = inv ? [len(shape3d)-1:-1:0] : [0:len(shape3d)-1],
            begin_cap = [ if(!bcap) [ for (i=rng1) i ] ],
            end_cap   = [ if(!ecap) [ for (i=rng2) i+len(shape3d)*(pathlen-1) ] ] )
    [ sweep_points, concat(loop_faces, begin_cap, end_cap) ] ;

module sweep(shape, path_transforms, closed=false) {
    polyh = sweep_polyhedron(shape, path_transforms, closed) ;
    polyhedron(
        points = polyh[0], 
        faces  = polyh[1], 
        convexity = 5
    );
}

module sweep_sections(shape, path_transforms) {
    pathlen  = len(path_transforms);
    segments = pathlen + (closed ? 0 : -1);
    shape3d  = to_3d(shape);
    sweep_points = [ for ( i=[0:pathlen-1], pts = transform(path_transforms[i], shape3d) ) pts ];
    sections_facets = let (facets = len(shape3d))
                      [ for( i=[0:pathlen-1])
                            [ for( j=[0:facets-1] ) facets*i + j ] ];
    polyhedron(
        points = sweep_points,
        faces  = sections_facets,
        convexity = 5
    );
}
