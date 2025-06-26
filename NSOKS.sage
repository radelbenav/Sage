###############################################################################
#
# This is an implementation of NSOKS as appears in the paper 
#
# AN ALGORITHM FOR CONSTRUCTING AND CLASSIFYING
# THE SPACE OF SMALL INTEGER WEIGHING MATRICES. "https://arxiv.org/pdf/2304.09495"
#
# Usage: Nsoks(n,r,maxsq=-1) returns a list of lists, where each list is a representation of the form [(s1,m1),(s2,m2),...,(sk,mk)] where
# the si are the squares and the mi are their multiplicities, such that sum(si* mi)=n and sum(mi)=r.
# The parameter maxsq is the maximum square to use, and defaults to -1, which means no limit.
#
################################################################################



def Nsoks(n,r,maxsq=-1): 
    if n==0:
        return [[(0,r)]]
    if maxsq==0:
        return []
    if maxsq==1:
        if r>=n:
            return [[(1,n),(0,r-n)]]
        else:
            return []
    n0=RDF(n)
    M=floor(sqrt(n0))
    if maxsq!=-1: M=min(M,maxsq)
    L=ceil(sqrt(n0/r))
    if L>M:
        return []
    Lsqr=[]
    for s in range(L,M+1):
        s2=s^2
        ns=floor(n0/s2)
        if ns>r:
            continue
        if ns<1:
            break
        for i in range(1,ns+1):
            nnew=n-i*s2
            if i==r:
                Lsqr.append([(s,r)])
            else:
                rem=sum_of_sqrs(nnew,r-i,maxsq=s-1)
                if rem==[]:
                    continue
                #print(rem)
                for lsqr in rem:
                    #print (s,[(s,i)]+[lsqr])
                    Lsqr.append([(s,i)]+lsqr)
    return Lsqr
