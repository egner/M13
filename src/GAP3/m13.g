# M13, SE, 5.8.97, GAP v3.4

# Reference
#   [1] J. H. Conway: M_13.
#       in R. A. Bailey (ed.): Surveys in Combinatorics, 1997
#       London Math. Soc. Lect. Notes Series 241 (1997).

# projective plane PG(2,3)
# ========================

# the base field
F := GF(3);

# the points of the projective geometry
points := 
  Set(List(
    Filtered(
      Cartesian(Elements(F), Elements(F), Elements(F)),
      x -> x <> 0*x
    ),
    x -> RowSpace(F, [ x ])
  ));

# the lines of the projective geometry
lines := 
  Set(List(
    Filtered(
      Cartesian(Elements(F), Elements(F), Elements(F)),
      a -> a <> 0*a
    ),
    a -> Filtered(points, x -> x.generators[1] * a = F.zero)
  ));

# move
# ====

# s represents the state such that s[i] is the
#   label (in [1..13]) at point points[i] for all i.
#   The hole is the label 13.
# m represents a move by specifying a non-hole label (1..12) 
#   which is moved to the position of the hole.

move := function ( s, m )
  local iHole, im, sm, L, L1, iu, iv;

  # get indices in s of hole and m
  iHole := Position(s, 13);
  im    := Position(s, m);

  # swap the labels hole and m
  sm        := ShallowCopy(s);
  sm[iHole] := s[im];
  sm[im]    := s[iHole];

  # find the line containing [hole] and [m]
  L := 
    First(
      lines, 
      L -> points[iHole] in L and points[im] in L
    );
  L1 := Difference(L, [points[iHole], points[im]]);
  iu := Position(points, L1[1]);
  iv := Position(points, L1[2]);

  # swap the labels on u and v
  sm[iu] := s[iv];
  sm[iv] := s[iu];

  return sm;
end;

# hole-stabilizer M12
# ===================

if not IsBound(triangleMoves) then
  Print("#I forming triangle moves\n");

  # build the triangle moves (which do not collide)
  triangleMoves := [ ];
  for a in [1..12] do
    for b in [1..12] do
      m := move(move([1..13], a), b);
      if m[13] = a then
	Add(triangleMoves, [ PermList(move(m, a)), [a, b, a] ]);
      fi;
    od;
  od;
  triangleMoves := Set(triangleMoves);

  Print("#I forming M12\n");
  M12 := Group(List(triangleMoves, sw -> sw[1]), ());
  M12.abstractWords :=
    List(
      triangleMoves, 
      sw -> sw[2]
    );
  M12.abstractGenerators := 
    AbstractGenerators("g", Length(triangleMoves));

fi;

# 
# [ g1, g10^-1, g100^-1, g11, g13, g15, g17^-1, g21^-1, g23, g25^-1, g29, 
#   g3^-1, g31, g33^-1, g35, g37^-1, g41^-1, g45^-1, g49^-1, g5, g53^-1, 
#   g57^-1, g61^-1, g65^-1, g69^-1, g7, g73^-1, g10^-1*g1^-1, g10^-1*g17^-1, 
#   g11*g25, g21^-1*g1^-1, g21^-1*g19^-1, g3*g1, g91*g95, g91*g97, g95*g93, 
#   g97*g91, g10*g100*g91, g10*g100*g93, g101*g107*g25, g101*g107*g27, 
#   g10*g37*g49^-1*g39^-1, g10*g43*g23^-1*g49^-1, g100*g75*g35^-1*g45^-1, 
#   g101*g85*g37^-1*g55^-1 ]


# searching the orbit graph
# =========================

search := function ( from )
  local shortest, agenda, s, w, agendaInc, m, i, sm, wm;

  shortest := [ ];
  agenda   := [ [[1..13], [ ]] ];
  while Length(agenda) > 0 do

    # report
    Print(Length(agenda), " \c");
    if Length(shortest) = 1000 then return; fi;

    # get state from agenda
    s := agenda[1][1];
    w := agenda[1][2];
    agenda := Sublist(agenda, [2..Length(agenda)]);

    # consider all moves from s
    agendaInc := [ ];
    for m in [1..12] do
      sm := move(s, m);
      i  := Position(shortest, sw -> sw[1] = sm);
      if i = false then
        wm := ShallowCopy(w);
        Add(wm, m);

        Add(shortest,  [sm, wm]);
        Add(agendaInc, [sm, wm]);
      fi;
    od;
    Append(agenda, agendaInc);
  od;

  return shortest;
end;
