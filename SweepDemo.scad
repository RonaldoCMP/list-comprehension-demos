use <sweep.scad>

////////////////////////////////////////////
//
//  This demo illustrates the effect of four path transform functions
//  on the final sweep. The path transform considered are:
//      - for "non constraint":     construct_transform_path()
//      - for "angle constrained":  adjusted_rotations()
//      - for "on surface":         referenced_path_transforms()
//      - for "vector constrained"  adjusted_directions()
//
//  Three different examples of sweeps are included:
//      - sweep on a cylindrical helix
//      - sweep of a torus knot
//      - sweep on the surface of a function graph
//
//  For better interaction, it is recommended to run the code with the
//  customizer snapshot version 2016.08.18.
//
//      Written by Ronaldo Persiano
//
/////////////////////////////////////////////////

/////////// Customizer Parameters //////////////

/* [0. Description] */
// Ilustrates the extra functions in sweep2.scad to build path transforms for a path on a surface.
Example = "Helix sweep"; // ["Helix sweep", "Torus knot", "Sweep on Surface"]

/* [1. Section parameters] */
section_shape          = "circular"; // [circular, star, half circle]
section_discretization = 12; // [3:36]
section_radius         = 30; // [5:40]

/* [2. Path parameters] */
// for all
path_discretization    = 20; // [10:100]
// for Torus knot
closed_path            = false; // [true, false]
// for Helix
helix_turns            = 3; // [0.4:0.1:3]
// Torus knot parameter (p,q)
knot = [2,3]; // 

/* [3.Sweep parameters] */
// constraint type on sweeping
sweep_constraint = "on surface"; // [no constraint, angle constrained, vector constrained, on surface]
// for angle constrained only
twist_turns   = 0; // [-3:3]
// for angle constrained only
initial_angle = 0; // [-180:180]
// for open paths and angle constrained only
final_angle   = 0;   // [-180:180]
// initial reference vector for vector constrained only
ref_ini = [0,0,100];
// final reference vector for vector constrained only
ref_end = [0,0,100];

/* [4. Surface parameters] */
// Undelying surface mesh size
surface_discretization = 50; // [10:80]

/* [5. Visualization parameters] */
// Show just the sections mapped by sweep
show_sections = false;
// Sweep frame: x red, y green, path blue, tangent not shown
show_frame = false;
// Sweep 
show_sweep = true;
// Undelying surface
show_surface = true; // 
/* [Hidden] */

/////////// Code starts here //////////////////
sd = section_discretization;
sr = section_radius;
pd = path_discretization;
if(Example=="Helix sweep") {
    // helix data
    R     = 300;
    pass  = 300;
    turns = helix_turns;
    if(show_surface) %cylinder(r=R, h=1.1*turns*pass, $fn=surface_discretization);
    path    = [for(i=[0:turns*pd]) let(a = i/pd)
                [R*cos(360*a), R*sin(360*a), a*pass] ];
    normals = [for(i=[0:turns*pd]) let(a = i/pd)
                [R*cos(360*a), R*sin(360*a), 0] ];
    do_sweep(path, normals, false);
}
if(Example=="Torus knot") {
    // Torus and knot data
    R = 400;
    r = 150;
    p = knot[0];
    q = knot[1];
    if(show_surface) %torus(R,r);
    k = max(p , q) * pd;   
    kc = closed_path ? 0 : 1;
    path    = [ for (i=[0:k-1-kc]) 
                knot(360*(i/(k-1))/gcd(p,q),R,r,p,q) ];
    normals = [ for (i=[0:k-1]) 
                knot_normal(360*i/(k-1)/gcd(p,q),R,r,p,q) ];
    do_sweep(path, normals, closed_path);
}
if(Example=="Sweep on Surface") {
    // the surface mesh
    nx = surface_discretization; 
    ny = surface_discretization;
    xmax = 500; ymax = 500;
    if(show_surface) {
        mesh = [for(i=[0:nx])
                [for(j=[0:ny])
                  let( x = -xmax+2*i*xmax/nx,
                       y = -ymax+2*j*ymax/ny )
                  [x, y, surface(x/xmax,y/ymax)] ] ];
        %draw_mesh(mesh,thickness=0);
    }
    // path on surface
    x0=[-xmax/2,-ymax];
    x1=[ xmax,   ymax];
    path=[for(i=[0:pd]) 
            let( x = x0[0]*(1-i/pd) + x1[0]*i/pd,
                 y = x0[1]*(1-i/pd) + x1[1]*i/pd )
            [ x, y, surface(x/xmax,y/ymax)] ];
    // normal at path points
    normals = [for(p=path) surf_normal(p[0]/xmax, p[1]/ymax, xmax,ymax) ];
    do_sweep(path, normals, false);
}

module do_sweep(path, normals, closed, tgts) {
    path_transf = construct_transform_path(path, closed, tgts);
    tot_ang     = 
        closed ? 
            360*twist_turns : 
            final_angle-initial_angle+360*twist_turns;
    adjusted_transf = 
        sweep_constraint == "angle constrained" ?
            adjusted_rotations( path_transf, 
                                angini = initial_angle, 
                                angtot = tot_ang, 
                                closed = closed):
        sweep_constraint == "vector constrained" ?
            adjusted_directions(path_transf, v0=ref_ini, vf=ref_end, turns=twist_turns, closed=closed) :
        sweep_constraint == "on surface" ?
            referenced_path_transforms(path, normals) :
            path_transf;
    
    if(show_frame) {
        projct = [[1,0,0,0],[0,1,0,0],[0,0,1,0]]; 
        framex = 100*[for(transf=adjusted_transf) projct*transf*[1,0,0,0]];
        framey = 100*[for(transf=adjusted_transf) projct*transf*[0,1,0,0]];
        for(i=[0:len(path)-1]) {
            color("red")   line(path[i],path[i]+framex[i], t= 10);
            color("green") line(path[i],path[i]+framey[i], t= 10);
        }
        color("blue") polyline(path, t=10);
    }
    if(show_sections) sweep_sections(section(), adjusted_transf, closed=closed);
    else if(show_sweep) sweep(section(), adjusted_transf, closed=closed);
}

function section() =
    section_shape=="circular" ?
        [for(i=[0:sd-1]) sr*[cos(i*360/sd), sin(i*360/sd)] ] :
    section_shape=="half circle" ?
        [for(i=[0:sd-1]) sr*[cos(i*180/(sd-1)),sin(i*180/(sd-1))] ]: 
    sr*[ [0,1], [-1/4,1/4], [-1,0], [-1/4,-1/4], 
         [0,-1], [1/4-1/4], [1,0],[1/4,1/4] ];

////////////////////////
// Torus knot functions

function knot(phi,R,r,p,q) = 
    [ (r * cos(q * phi) + R) * cos(p * phi),
      (r * cos(q * phi) + R) * sin(p * phi),
       r * sin(q * phi) ];

function knot_normal(phi,R,r,p,q) =  
    knot(phi,R,r,p,q) 
        - R*unit(knot(phi,R,r,p,q)
            - [0,0, knot(phi,R,r,p,q)[2]]) ;

function gcd(a, b) = (a == b)? a : (a > b)? gcd(a-b, b): gcd(a, b-a);

module torus(R,r){
    rotate_extrude() translate([R,0,0]) circle(r);
}
////////////////////////
// Surface functions

function surface(x,y) =
    10*(40 - 25*x*x - 25*y*y)*cos(180*x)*cos(180*y);

function dsurfdx(x,y) =
    -500*x*cos(180*x)*cos(180*y)
    - 10*(40 - 25*x*x - 25*y*y)*cos(180*y)*sin(180*x)*PI;

function dsurfdy(x,y) = dsurfdx(y,x);

function surf_normal(x,y,xmax,ymax) =
    [ -dsurfdx(x,y)/xmax, -dsurfdy(x,y)/ymax, 1]; // cross product

/////////////////////////
// Drawing modules for preview only
module draw_mesh(mesh) {
  n = len(mesh) != 0 ? len(mesh) : 0 ;
  m = n==0 ? 0 : len(mesh[0]) != 0 ? len(mesh[0]) : 0 ; 
  l = n*m;
  if( l > 0 ) {
    vertices = [ for(line=mesh) for(pt=line) pt ];     
    tris = concat(   [ for(i=[0:n-2],j=[0:m-2]) 
                        [ i*m+j, i*m+j+1, (i+1)*m+j ] ] ,
                     [ for(i=[0:n-2],j=[0:m-2]) 
                        [ i*m+j+1, (i+1)*m+j+1, (i+1)*m+j ] ] );
                   
    polyhedron(
        points = vertices,
        faces  = tris,
        convexity = 10
    ); 
  }
}
module line(p0, p1, t=1) {
    v = p1-p0;
    translate(p0)
        // rotate the cylinder so its z axis is brought to direction v
        multmatrix(rotate_from_to([0,0,1],v))
            cylinder(d=t, h=norm(v), $fn=4);
}

module polyline(p,t=1) {
    for(i=[1:1:len(p)-1]) line(p[i-1],p[i],t);
}
