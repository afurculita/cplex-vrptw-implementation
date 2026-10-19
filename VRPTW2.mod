/*****************************************************************************
 *
 * Vehicle Routing Problem with Time Windows (VRPTW)
 * Two-index formulation for a homogeneous fleet.
 *
 * Compared with the three-index model in VRPTW.mod the vehicle index is
 * dropped: x[<i,j>] = 1 if *some* vehicle travels from i to j.  Capacity is
 * enforced with Miller-Tucker-Zemlin load variables u[i] (load of the vehicle
 * after serving i) and time windows with start-of-service variables s[i].
 * The model has v times fewer arc variables and no vehicle symmetry, so it
 * is the formulation of choice when the vehicles are identical.
 *
 * Arcs are a sparse tuple set: only time-compatible arcs get a variable.
 * Time windows are tightened in preprocessing and the objective is the
 * Solomon benchmark convention: fewest vehicles first, then shortest
 * distance (staticLex).  Uses the same .dat files as VRPTW.mod.
 *
 * Written for IBM ILOG CPLEX Optimization Studio 22.2.
 *
 *****************************************************************************/

/*****************************************************************************
 * DATA
 *****************************************************************************/

int   v        = ...;       // number of identical vehicles

int   CustomersNumber = ...;
range Customers       = 1..CustomersNumber;
range Nodes           = 0..CustomersNumber+1;
int   Depot           = 0;
int   EndDepot        = CustomersNumber + 1;

int Capacity          = ...;
int Demand[Customers] = ...;

int LBTW[Nodes]        = ...;
int UBTW[Nodes]        = ...;
int ServiceTime[Nodes] = ...;
int XCoord[Nodes]      = ...;
int YCoord[Nodes]      = ...;

float Distance[i in Nodes][j in Nodes] =
  floor(sqrt((XCoord[i] - XCoord[j]) * (XCoord[i] - XCoord[j])
           + (YCoord[i] - YCoord[j]) * (YCoord[i] - YCoord[j])) * 10) / 10.0;

float Time[i in Nodes][j in Nodes] = Distance[i][j] + ServiceTime[i];

// Time-window tightening, see VRPTW.mod for the explanation.
float Ready[Nodes];
float Due[Nodes];
execute TIGHTEN_TIME_WINDOWS {
  for (var i in Nodes) {
    Ready[i] = LBTW[i];
    Due[i] = UBTW[i];
  }
  var changed = true;
  var rounds = 0;
  while (changed && rounds < 100) {
    changed = false;
    rounds = rounds + 1;
    for (var j in Customers) {
      var earliest = Infinity;
      for (var i in Nodes) {
        if (i != j && i != EndDepot && Ready[i] + Time[i][j] <= Due[j]) {
          earliest = Math.min(earliest, Ready[i] + Time[i][j]);
        }
      }
      if (earliest != Infinity && earliest > Ready[j] + 1e-9) {
        Ready[j] = earliest;
        changed = true;
      }
      var latest = -Infinity;
      for (var k in Nodes) {
        if (k != j && k != Depot && Ready[j] + Time[j][k] <= Due[k]) {
          latest = Math.max(latest, Due[k] - Time[j][k]);
        }
      }
      if (latest != -Infinity && latest < Due[j] - 1e-9) {
        Due[j] = latest;
        changed = true;
      }
    }
  }
}

// Sparse arc set: no self loops, nothing into the depot, nothing out of the
// end depot, no empty route 0 -> n+1 and only time-compatible arcs.
tuple Arc {
  int i;
  int j;
}
{Arc} Arcs = { <i, j> | i, j in Nodes :
                 i != j && j != Depot && i != EndDepot
                 && !(i == Depot && j == EndDepot)
                 && Ready[i] + Time[i][j] <= Due[j] };

float BigM[a in Arcs] = maxl(0, Due[a.i] + Time[a.i][a.j] - Ready[a.j]);
float TotalDemand = sum(i in Customers) Demand[i];

/*****************************************************************************
 * DECISION VARIABLES
 *****************************************************************************/

dvar boolean x[Arcs];                                   // arc used by a vehicle
dvar float   s[i in Nodes] in Ready[i]..Due[i];         // start of service at i
dvar float   u[i in Customers] in Demand[i]..Capacity;  // vehicle load after serving i

dexpr float TotalDistance = sum(a in Arcs) Distance[a.i][a.j] * x[a];
dexpr int   VehiclesUsed  = sum(a in Arcs : a.i == Depot) x[a];

/*****************************************************************************
 * SOLVER SETTINGS
 *****************************************************************************/

execute PARAMS {
  cplex.tilim = 600;
  cplex.epgap = 1e-4;
}

/*****************************************************************************
 * MODEL
 *****************************************************************************/

// Fewest vehicles first, then shortest distance.  Use "minimize TotalDistance;"
// to minimise the distance only.
minimize staticLex(VehiclesUsed, TotalDistance);

subject to {

  // Each customer is entered and left exactly once
  forall(j in Customers)
    ctArrive:
      sum(a in Arcs : a.j == j) x[a] == 1;
  forall(i in Customers)
    ctLeave:
      sum(a in Arcs : a.i == i) x[a] == 1;

  // Fleet size
  ctFleet:
    VehiclesUsed <= v;

  // Capacity cut: at least ceil(total demand / capacity) vehicles are needed
  ctMinVehicles:
    VehiclesUsed >= ceil(TotalDemand / Capacity);

  // Time propagation (also eliminates sub-tours)
  forall(a in Arcs)
    ctTimePropagation:
      s[a.i] + Time[a.i][a.j] - BigM[a] * (1 - x[a]) <= s[a.j];

  // Load propagation between consecutive customers (Miller-Tucker-Zemlin)
  forall(a in Arcs : a.i != Depot && a.j != EndDepot)
    ctLoadPropagation:
      u[a.i] + Demand[a.j] - Capacity * (1 - x[a]) <= u[a.j];
}

/*****************************************************************************
 * OUTPUT
 *****************************************************************************/

execute DISPLAY {
  writeln("Total distance: ", TotalDistance);
  writeln("Vehicles used: ", VehiclesUsed, " of ", v);
  var r = 0;
  for (var a in Arcs) {
    if (a.i == Depot && x[a] > 0.5) {
      r = r + 1;
      var node = a.j;
      var line = "route " + r + ": " + Depot + " -> " + node + "@" + s[node];
      var steps = 0;
      while (node != EndDepot && steps <= CustomersNumber) {
        for (var b in Arcs) {
          if (b.i == node && x[b] > 0.5) {
            node = b.j;
            line = line + " -> " + node + "@" + s[node];
            break;
          }
        }
        steps = steps + 1;
      }
      writeln(line);
    }
  }
}
