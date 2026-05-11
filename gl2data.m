/*
    This file implements the following function:
    GL2Load(N) -- loads subgroup data created by GL2Data, returning an associative array X indexed by label.
                  The input parameter can be either a prime l (indicating the file gl2_ladic.txt) or a filename.

    Much of it is stolen from the corresponding RSZB code.
*/
gl2rec := recformat<
    label:MonStgElt,        // label of the form N.i.g.n or N.i.g.d.n
    level:RngIntElt,        // level N
    index:RngIntElt,        // index i
    genus:RngIntElt,        // genus g
    subgroup:GrpMat,        // subgroup of GL(2,N)
    parents:SeqEnum,        // labels of groups of which this is a maximal subgroup
    name:MonStgElt          // name of the group if applicable (default is empty string)
>;

/* parsing functions that are faster and safer than using eval */
function strip(s) return Join(Split(Join(Split(s," "),""),"\n"),""); end function;
function atoi(s) return StringToInteger(s); end function;
function atoii(s) return [Integers()|StringToInteger(n):n in Split(t[2..#t-1],",")] where t:=strip(s); end function;
function atoiii(s)
    return [[Integers()|StringToInteger(n):n in Split(a[1] eq "]" select "" else Split(a,"]")[1],",")]:a in r] where r := Split(t[2..#t-1],"[") where t:= strip(s);
end function;
function labels(s) return Split(s[2..#s-1],","); end function;

function entry_to_rec(s)
    /* 
        Input: line from gl2data.txt
        Output: gl2rec
    */
    entry := Split(s, ":");
    Nig := Split(entry[1], "."); N := atoi(Nig[1]); i := atoi(Nig[2]); g := atoi(Nig[3]);
    H := GL2FromGenerators(N, i, atoiii(entry[2]));
    return rec<gl2rec|label:=entry[1],level:=N,index:=i,genus:=g,subgroup:=H,parents:=labels(entry[3]),name:=((entry[4] eq "None") select entry[1] else entry[4])>;
end function;
XX := [entry_to_rec(line) : line in Split(Read("gl2data.txt"))]; XX := [k : k in XX | k`genus gt 1];
XX_zyw := Split(Read("gl2data_zywina_a2.txt"));