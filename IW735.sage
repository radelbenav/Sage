# File Name: SageCheckIWnkViaILPAgainstSignedPermutationsDate29082022Ver01.txt
# Purpose: Check (Integer) Weighing matrices Via Integer Linear Programming against (direct) Signed permutations
# Remark: After session with Radi. We are left with a question:
#         Why No solution for R1,R2:  [0, 0, 0, 0, 0, 0, 5] [0, 0, 2, 2, 2, 2, 3]
# Improvements: (1) Problem from remark fixed.
#               (2) Added "sors" routine from Assaf, so to generalize the whole activity.
# Remark: Radi on 8/5/22 noticed that solutions begin with negative values although BegWithPos should prevent it.
#         We fix it.
# Remark: On 12/5/22 we added two routines
#         OurMain2: Given parameters of weighing matrix, weight and 2 divisors of order, it gives all pairs of
#                   orthogonal rows of all types available of nsoks and filter them by the code invariany method.
#         AddLine:  Given Nsoks and Sols gives all additions to Sols by one row taken from Nsoks
#                   with permutations and signings and codeinvariant.
#                   This routine is the basis for recursion to construct all Integer Weighing Matrices.
#                   We have not run and debugged this routine yet. Next time...
# Remark: On 15/5/22 we wroteqimproved/touched some routines:
#         OurMain2: This is the new main. It gets the [WMweight, WMOrderDiv] of a weighing matrix and should output all inequivalent Integer weighing matrices of order=WMOrderDiv & weight=sqrt(WMweight. 
#         FilterOrthogonalSignedPermutationsAgainstMatrix (haven't debugged yet)
#         CodePrevRows (debugged carefully)
# Remark: On 26052022 we debuged OurMain2 routine.
# Remark On 30-6-22 Organizing the hp check. 
#                   automatic base calculation for the code invariant
#                   indexing the permutation and signs and saving the index in the configuration.
# Remark on 3-7-22 Adding code to check for Hadamrd equivalnce for two rows for permutation AND row negation
#                  Changes in "FilterOrthogonalSignedPermutationsByCodeInvariant" adding two code invariants for each line.
# Remark on 14-7-22 Adding the index for each line of (NsoksIndex,PermutationIndex,SignsIndex) 
#                    Bug for line [3, 2, 2, 2, 2, 0, 0], [[1, 16, 5], (2, -3, 2, -2, 0, 2, 0)]], 
#                                 The SignsIndex looks incorrect - TBD in the next meeting
# Remark on 21-7-22 Generelizing for AboveMatrix.
#                    -   OrthogonalSignedPermutationsWithFirstNonZeroPositiveAgainstMatrix
#                    -   normAboveAgainstMatrix(AboveMatrix,R2):
#                    -   dpAgainstMatrix
#                       need to correct FilterOrthogonalSignedPermutationsByCodeInvariantAgainstMatrix
# Remark on 24-7-22  began adapting FilterOrthogonalSignedPermutationsByCodeInvariantAgainstMatrix
#                    adding routine genCode for generating a code for the column i.
#                   for next time - continue to adapt  FilterOrthogonalSignedPermutationsByCodeInvariantAgainstMatrix
#                                    and remove CodePrevRows
# Remark on 31-7-22 remove CodePrevTows and AddLine
#                   Checked FilterOrthogonalSignedPermutationsByCodeInvariantAgainstMatrix for addition of one row.
#                   Coded OurMain3 to work with FilterOrthogonalSignedPermutationsByCodeInvariantAgainstMatrix
#                   Checked OurMain3 for two lines.
# Remark on 31-7-22 Adapt OurMain3 for 7 lines
#                   While running OurMain3 it works fine for 2 and 3 lines but crashes while
#                             calculating for 4 lines in memory shortage
# Remark on 18-7-22 Cleanup
# Remark on 28-8-22 
#                  integrate   FilterOrthogonalSignedPermutationsByCodeInvariant
#                           to OrthogonalSignedPermutationsWithFirstNonZeroPositiveAgainstMatrix
#                  integrate hp into OrthogonalSignedPermutationsWithFirstNonZeroPositiveAgainstMatrix
#                  integrate gencode also
#                  add goodPerm test to eliminate (-1) assignment to 0 (faster)


def HadamardSpace(d): #Return a list of all Hadamard (+-1)-vectors of size d that begin with -1.
    SpaceSize = 2^(d-1)
    L=[ZZ(n).digits(2) for n in range(SpaceSize)]
    L1 = [x+[0]*(d-len(x)-1) for x in L]
    return([[-1]+[2*y-1 for y in x] for x in L1])

def IsBegWithPos(L): #Returns True if L[0]>0. Otherwise return False.
    for x in L:
        if x>0:
            return(True)
        if x<0:
            return(False)
    return(False)

def goodPerm(L,s):#Given two lists L,s of the same length, check that there is no -1 in s corresponding to 0 in L.
    for i in range(len(L)):
        if (L[i]==0) and (s[i]==-1) : return False
    return True

def normAboveAgainstMatrix(AboveMatrix,R2):#AboveMatrix is a given IW partial matrix. R2 is a new row that we want to add to the matrix. We normalize R2[i]<0 if the column above it in AboveMatrix is zero.
    for i in range(len(R2)):
        if AboveMatrix.column(i).norm()==0:
            R2[i]=-abs(R2[i])
    return R2

def normAbove(myMAT):#MyMat is a given IW partial matrix. We normalize each column of MyMat to begin with a negative entry.
    for i in range(myMAT.ncols()):
        for j in range(myMAT.nrows()):
            if myMAT[j,i]!=0:
                myMAT[j,:]*=-sign(myMAT[j,i])
                break
    return myMAT

def dpAgainstMatrix(AboveMatrix,L2): #We compute the norm of the product of L2 (a candidate ro given in a list form) against the rows of AboveMatrix.
    return((AboveMatrix*vector(L2)).norm())


def orderMat(SPMat,base):#This procedure reorders the columns of SPMat (a partial IW) by increasing lex order. We interpret each column as represention of a number in base 'base'. This entry should be sufficiently large to accomodate all possible entries in the matrix. 
    nR=SPMat.nrows();
    baseVec = vector([base^(nR-j) for j in range(nR)])  
    SPMat=normAbove(SPMat)
    SPMat=sorted(SPMat.columns(),key=lambda vec:baseVec*vec)
    return matrix(SPMat).transpose()  
    
    
def OrthogonalSignedPermutationsWithFirstNonZeroPositiveAgainstMatrix(AboveMat,L,Lindex,MaxV):
    """
    This precedure produces a list of all vectors of type L (i.e. Hadamard equivalent to L) that are orthogonal to AboveMat.
    Input:
          AboveMat = a partial IW matrix.
          L = The given type of the orthogonal row.
          Lindex = The index of L in the list of 'sors'.
          maxV = An upper bound of all modulii of all matrix entries.

    Output: A list of pairs: ( [index in sors, index in permutations, index in signings], new orthogonal row)
    """
    P = Permutations(L).list()
    d = len(L)
    S = HadamardSpace(d)
    ln=AboveMat.nrows()+1
    SL=[diagonal_matrix(v)*p.matrix() for v in HadamardSpace(ln) for p in SymmetricGroup(ln)]
    SL = HadamardSpace(AboveMat.nrows()+1)
    SP = []
    s = []
    sd = [] 
    codeBase = 1+2*MaxV
    nR=AboveMat.nrows()
    cB=(vector([codeBase^(nR-j) for j in range(nR)]))*AboveMat
    for pi in range(Lindex[1],len(P)):
        p = P[pi]
        #s0=Lindex[2] if pi==Lindex[1] else 0
        s0=0
        for si in range(s0,len(S)):
            sn=S[si]
            if (goodPerm(p,sn)): #Take only the signing at nonzero entries of the vector. This save a lot of time.
                r =[p[i]*sn[i] for i in range(d)]
                if true:
                    if dpAgainstMatrix(AboveMat,r)==0: # Is the vector orthogonal.
                        #r=normAboveAgainstMatrix(AboveMat,r)
                        NewMat=matrix(nR+1,d,AboveMat.list()+r)
                        signedPermutaionsM = [ diagonal_matrix(v)*p.matrix() for v in HadamardSpace(nR+1) for p in SymmetricGroup(nR+1)]
                        for sPM in signedPermutaionsM:
                            OrederedSnewMat=orderMat(sPM*NewMat) #This is for the new algorithm (TODO: continue)
                        if not(r in SP):
                            SP.append(r)
                            R2i=vector(r)
                            M1 = cB+R2i #This computes the new code invariant of the (potential) augmented matrix.
                            M1s = sorted(M1)
                            if not(M1s in s) :
                                M1m = cB-R2i #This is the same with -the row.
                                M1sm = sorted(M1m)
                                if not(M1sm in s): #Only consider row if it contributes new code invariant.
                                    s.append(M1s)
                                    sd.append([[Lindex[0],pi,si],R2i])                    
    return(sd)

def LEcodeVector(cv1,cv2): #This asks if two vectors cv1<=cv2 under the lex order (entries are ordered by integer ordering).
    for i in range(len(cv1)):
        if cv1[i]<cv2[i]: return true
        if cv1[i]>cv2[i]: return false
    return true


def sors(n,r,maxsq):  ### Find all ways to express n=\sum_i s_i^2 as a sum of r squares, with maxsq>=s_1>=s_2>=...>=s_r.
    #n0=RDF(n). This is NOT our best algorithm (TODO: look for the more recent 'nsoks').
    n0=n
    if r==1:
        s=sqrt(n0)
        fs=floor(s)
        if s==fs and s<=maxsq:
            return [[s]]
        else:
            return false
    else:
        sors2=[]
        for x in range(floor(sqrt(n0/r)),min(floor(sqrt(n0)),maxsq)+1):
            m=n-x^2
            #print x
            sors1=sors(m,r-1,x)
            if sors1:
                sors2+=[[x]+sors1[i] for i in range(len(sors1))   ]
           # print "sors2=",sors2
        if len(sors2)>0:
            return sors2
        else:
            return false


def OurMain3(WMWeight, WMOrderDiv,lines): 
    """
    Return a list of (partial) IW matrices of a given size.

    Input: WMWeight = the desired weight.
           WMOrderDiv = the row size.
           lines = the column size.

    Output: A list of IW matrices with the given parameters. The list is an exhaustive list of all possible solution up to Hadamard equivalence.
            It is possible though that the same Hadamard type will repeat more than once. 
    """
    MaxSquare = WMWeight^(1/2)
    A = sors(WMWeight, WMOrderDiv, MaxSquare) #This gives the list of all possible rows up to sign and ordering.
    AllSoks=[list(map(lambda x:-x , A[len(A)-i-1])) for i in range(len(A)) ] #This is just to represent each row by the minimal lex representative.
    print("Nsoks: ",AllSoks)
    Sols= [[matrix(1,WMOrderDiv,AllSoks[i]),[i,0,0]] for i in range(len(AllSoks))] #Sols is the list of pairs: A partial matrix and the index of its last row in Allsoks. We start with just 1 row per matrix, and update as we go through the main loop.
    print(Sols)
    for line in range(lines-1): #This is the main loop, which adds one row at a time to each matrix. 
        nSols=[]
        countSol=0
        countScan=0
        for Sol in Sols:
            countScan+=1
            AboveMat=Sol[0]
            R1Index=Sol[1]
            for R2i in range(R1Index[0],len(AllSoks)): # We want to add a new row, but one that appears later (or same) in Allsoks. This is because we can allow our final matrix to be monotonely increasing in Allsoks.
                R2Index=R1Index if R2i==R1Index[0] else [R2i,0,0]
                R2 = vector(AllSoks[R2i])
                cpF = OrthogonalSignedPermutationsWithFirstNonZeroPositiveAgainstMatrix(AboveMat,R2,R2Index,MaxSquare) #This gives a list of all rows which are Hadamard equivalent to R2 and orthogonal to AboveMat.
                countSol+=len(cpF)
                if len(cpF)>0:
                    nSols.extend([AboveMat,x] for x in cpF) #This is a list of pairs of AboveMat and its new row x.
            print("countScan,countSol  = ",countScan,countSol)
        Sols=[] #We now update Sols.
        for nSol in nSols:
            NL=matrix(WMOrderDiv,1,list(nSol[1][1])) #This practically adds the row to the matrix.
            AM=((nSol[0].transpose()).augment(NL)).transpose()
            Sols.append([AM,nSol[1][0]])
        print("# of sols in line",line, "  =",len(Sols),[Sols[i] for i in range(min(len(Sols),3))])
    return(Sols)

from gc import collect
collect()
#%time res=OurMain3(8,8,8)