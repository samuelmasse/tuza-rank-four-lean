import TuzaRankFour.Certificates.Cube
import TuzaRankFour.Certificates.Order10Skeleton06Adaptive.Formula
import TuzaRankFour.Certificates.Order10Skeleton06Adaptive.Leaf000000
import TuzaRankFour.Certificates.Order10Skeleton06Adaptive.Leaf000001
import TuzaRankFour.Certificates.Order10Skeleton06Adaptive.Leaf00001
import TuzaRankFour.Certificates.Order10Skeleton06Adaptive.Leaf0001
import TuzaRankFour.Certificates.Order10Skeleton06Adaptive.Leaf0010
import TuzaRankFour.Certificates.Order10Skeleton06Adaptive.Leaf0011
import TuzaRankFour.Certificates.Order10Skeleton06Adaptive.Leaf01000
import TuzaRankFour.Certificates.Order10Skeleton06Adaptive.Leaf01001
import TuzaRankFour.Certificates.Order10Skeleton06Adaptive.Leaf0101
import TuzaRankFour.Certificates.Order10Skeleton06Adaptive.Leaf011
import TuzaRankFour.Certificates.Order10Skeleton06Adaptive.Leaf100000
import TuzaRankFour.Certificates.Order10Skeleton06Adaptive.Leaf100001
import TuzaRankFour.Certificates.Order10Skeleton06Adaptive.Leaf10001
import TuzaRankFour.Certificates.Order10Skeleton06Adaptive.Leaf1001
import TuzaRankFour.Certificates.Order10Skeleton06Adaptive.Leaf1010
import TuzaRankFour.Certificates.Order10Skeleton06Adaptive.Leaf1011
import TuzaRankFour.Certificates.Order10Skeleton06Adaptive.Leaf110
import TuzaRankFour.Certificates.Order10Skeleton06Adaptive.Leaf111

namespace TuzaRankFour.Certificates.Order10Skeleton06Adaptive

theorem node00000 : ((((((formula).and (Sat.Fmla.one [Sat.Literal.neg 8])).and (Sat.Fmla.one [Sat.Literal.neg 11])).and (Sat.Fmla.one [Sat.Literal.neg 13])).and (Sat.Fmla.one [Sat.Literal.neg 14])).and (Sat.Fmla.one [Sat.Literal.neg 15])).proof [] :=
  Sat.Fmla.proof_empty_of_split ((((((formula).and (Sat.Fmla.one [Sat.Literal.neg 8])).and (Sat.Fmla.one [Sat.Literal.neg 11])).and (Sat.Fmla.one [Sat.Literal.neg 13])).and (Sat.Fmla.one [Sat.Literal.neg 14])).and (Sat.Fmla.one [Sat.Literal.neg 15])) 16
    leaf000000
    leaf000001

theorem node10000 : ((((((formula).and (Sat.Fmla.one [Sat.Literal.pos 8])).and (Sat.Fmla.one [Sat.Literal.neg 11])).and (Sat.Fmla.one [Sat.Literal.neg 13])).and (Sat.Fmla.one [Sat.Literal.neg 14])).and (Sat.Fmla.one [Sat.Literal.neg 15])).proof [] :=
  Sat.Fmla.proof_empty_of_split ((((((formula).and (Sat.Fmla.one [Sat.Literal.pos 8])).and (Sat.Fmla.one [Sat.Literal.neg 11])).and (Sat.Fmla.one [Sat.Literal.neg 13])).and (Sat.Fmla.one [Sat.Literal.neg 14])).and (Sat.Fmla.one [Sat.Literal.neg 15])) 16
    leaf100000
    leaf100001

theorem node0000 : (((((formula).and (Sat.Fmla.one [Sat.Literal.neg 8])).and (Sat.Fmla.one [Sat.Literal.neg 11])).and (Sat.Fmla.one [Sat.Literal.neg 13])).and (Sat.Fmla.one [Sat.Literal.neg 14])).proof [] :=
  Sat.Fmla.proof_empty_of_split (((((formula).and (Sat.Fmla.one [Sat.Literal.neg 8])).and (Sat.Fmla.one [Sat.Literal.neg 11])).and (Sat.Fmla.one [Sat.Literal.neg 13])).and (Sat.Fmla.one [Sat.Literal.neg 14])) 15
    node00000
    leaf00001

theorem node0100 : (((((formula).and (Sat.Fmla.one [Sat.Literal.neg 8])).and (Sat.Fmla.one [Sat.Literal.pos 11])).and (Sat.Fmla.one [Sat.Literal.neg 13])).and (Sat.Fmla.one [Sat.Literal.neg 14])).proof [] :=
  Sat.Fmla.proof_empty_of_split (((((formula).and (Sat.Fmla.one [Sat.Literal.neg 8])).and (Sat.Fmla.one [Sat.Literal.pos 11])).and (Sat.Fmla.one [Sat.Literal.neg 13])).and (Sat.Fmla.one [Sat.Literal.neg 14])) 15
    leaf01000
    leaf01001

theorem node1000 : (((((formula).and (Sat.Fmla.one [Sat.Literal.pos 8])).and (Sat.Fmla.one [Sat.Literal.neg 11])).and (Sat.Fmla.one [Sat.Literal.neg 13])).and (Sat.Fmla.one [Sat.Literal.neg 14])).proof [] :=
  Sat.Fmla.proof_empty_of_split (((((formula).and (Sat.Fmla.one [Sat.Literal.pos 8])).and (Sat.Fmla.one [Sat.Literal.neg 11])).and (Sat.Fmla.one [Sat.Literal.neg 13])).and (Sat.Fmla.one [Sat.Literal.neg 14])) 15
    node10000
    leaf10001

theorem node000 : ((((formula).and (Sat.Fmla.one [Sat.Literal.neg 8])).and (Sat.Fmla.one [Sat.Literal.neg 11])).and (Sat.Fmla.one [Sat.Literal.neg 13])).proof [] :=
  Sat.Fmla.proof_empty_of_split ((((formula).and (Sat.Fmla.one [Sat.Literal.neg 8])).and (Sat.Fmla.one [Sat.Literal.neg 11])).and (Sat.Fmla.one [Sat.Literal.neg 13])) 14
    node0000
    leaf0001

theorem node001 : ((((formula).and (Sat.Fmla.one [Sat.Literal.neg 8])).and (Sat.Fmla.one [Sat.Literal.neg 11])).and (Sat.Fmla.one [Sat.Literal.pos 13])).proof [] :=
  Sat.Fmla.proof_empty_of_split ((((formula).and (Sat.Fmla.one [Sat.Literal.neg 8])).and (Sat.Fmla.one [Sat.Literal.neg 11])).and (Sat.Fmla.one [Sat.Literal.pos 13])) 14
    leaf0010
    leaf0011

theorem node010 : ((((formula).and (Sat.Fmla.one [Sat.Literal.neg 8])).and (Sat.Fmla.one [Sat.Literal.pos 11])).and (Sat.Fmla.one [Sat.Literal.neg 13])).proof [] :=
  Sat.Fmla.proof_empty_of_split ((((formula).and (Sat.Fmla.one [Sat.Literal.neg 8])).and (Sat.Fmla.one [Sat.Literal.pos 11])).and (Sat.Fmla.one [Sat.Literal.neg 13])) 14
    node0100
    leaf0101

theorem node100 : ((((formula).and (Sat.Fmla.one [Sat.Literal.pos 8])).and (Sat.Fmla.one [Sat.Literal.neg 11])).and (Sat.Fmla.one [Sat.Literal.neg 13])).proof [] :=
  Sat.Fmla.proof_empty_of_split ((((formula).and (Sat.Fmla.one [Sat.Literal.pos 8])).and (Sat.Fmla.one [Sat.Literal.neg 11])).and (Sat.Fmla.one [Sat.Literal.neg 13])) 14
    node1000
    leaf1001

theorem node101 : ((((formula).and (Sat.Fmla.one [Sat.Literal.pos 8])).and (Sat.Fmla.one [Sat.Literal.neg 11])).and (Sat.Fmla.one [Sat.Literal.pos 13])).proof [] :=
  Sat.Fmla.proof_empty_of_split ((((formula).and (Sat.Fmla.one [Sat.Literal.pos 8])).and (Sat.Fmla.one [Sat.Literal.neg 11])).and (Sat.Fmla.one [Sat.Literal.pos 13])) 14
    leaf1010
    leaf1011

theorem node00 : (((formula).and (Sat.Fmla.one [Sat.Literal.neg 8])).and (Sat.Fmla.one [Sat.Literal.neg 11])).proof [] :=
  Sat.Fmla.proof_empty_of_split (((formula).and (Sat.Fmla.one [Sat.Literal.neg 8])).and (Sat.Fmla.one [Sat.Literal.neg 11])) 13
    node000
    node001

theorem node01 : (((formula).and (Sat.Fmla.one [Sat.Literal.neg 8])).and (Sat.Fmla.one [Sat.Literal.pos 11])).proof [] :=
  Sat.Fmla.proof_empty_of_split (((formula).and (Sat.Fmla.one [Sat.Literal.neg 8])).and (Sat.Fmla.one [Sat.Literal.pos 11])) 13
    node010
    leaf011

theorem node10 : (((formula).and (Sat.Fmla.one [Sat.Literal.pos 8])).and (Sat.Fmla.one [Sat.Literal.neg 11])).proof [] :=
  Sat.Fmla.proof_empty_of_split (((formula).and (Sat.Fmla.one [Sat.Literal.pos 8])).and (Sat.Fmla.one [Sat.Literal.neg 11])) 13
    node100
    node101

theorem node11 : (((formula).and (Sat.Fmla.one [Sat.Literal.pos 8])).and (Sat.Fmla.one [Sat.Literal.pos 11])).proof [] :=
  Sat.Fmla.proof_empty_of_split (((formula).and (Sat.Fmla.one [Sat.Literal.pos 8])).and (Sat.Fmla.one [Sat.Literal.pos 11])) 13
    leaf110
    leaf111

theorem node0 : ((formula).and (Sat.Fmla.one [Sat.Literal.neg 8])).proof [] :=
  Sat.Fmla.proof_empty_of_split ((formula).and (Sat.Fmla.one [Sat.Literal.neg 8])) 11
    node00
    node01

theorem node1 : ((formula).and (Sat.Fmla.one [Sat.Literal.pos 8])).proof [] :=
  Sat.Fmla.proof_empty_of_split ((formula).and (Sat.Fmla.one [Sat.Literal.pos 8])) 11
    node10
    node11

theorem nodeRoot : (formula).proof [] :=
  Sat.Fmla.proof_empty_of_split (formula) 8
    node0
    node1

theorem refutation : formula.proof [] := nodeRoot

end TuzaRankFour.Certificates.Order10Skeleton06Adaptive
