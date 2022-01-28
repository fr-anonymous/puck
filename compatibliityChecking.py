#!/usr/bin/python3

import TACQ
from TACQ import TACQ
import argparse
import constraint
from constraint import Problem
from datetime import datetime


"""
Comptatibility checking between Privacy and Utility policies

usage: CompatibiltyChecking.py [-h|--help] [-v|--verbose] [-p|--privacy <file>] [-u|--utility <file>]

arguments:
  -h | --help    : Show this help and exit
  -v | --verbose : Explain each step
  -p | --privacy : file containing the privacy query, default value is 'privacy.sparql'
  -u | --utility : file containing the utility queries, default value is 'utility.sparql'
"""

def readTACQs(file, prefix):
    """
    Extracts queries from a file.

    inputs: - file name
            - prefix for query names
    output: - dictionary of numbered TACQs
    """
    if not isinstance(file, str):
        raise TypeError('The "file" parameter of reqdQueries() must be a string !')
    if not isinstance(prefix, str):
        raise TypeError('The "prefix" parameter of reqdQueries() must be a string !')

    queries = []
    TACQs = {}
    qNum = 1
    
    # read the file
    inputFile = open(file)
    lines = inputFile.readlines()
    # convert it into a string (easier to split)
    content = ''
    for l in lines:
        content = content + ' ' + l
    # check that there is a SELECT in the file
    first = content.find('SELECT')
    if first == -1:
        raise Exception('No SELECT in the file !')
    rest = content[first:]
    queries = rest.split('SELECT')
    # remove empty queries
    while '' in queries:
        queries.remove('')
    # convert queries into TACQs
    for q in queries:
        q = 'SELECT' + str(q)
        tacq = TACQ()
        tacq.parse(q)
        TACQs[prefix + str(qNum)] = tacq
        qNum = qNum + 1
    return TACQs



def checkTheorem41(PQ, unionUQs):
    """
    Check compatibility according to Therorem 4.1 and 4.3 (overlaping GPs)

    inputs: - PQ  : a privacy query
            - UQs : a dictionary of utility queries 
    output: - a dictionnary { compatible, reasons } where:
                - compatible is a boolean
                - reasons is a dictionary associating line numbers to a list of couple of constants 
                   that must be equated to return a result 
              ex : { "compatible' : false, 'reasons' : { 1 : [(oc1, oc2), (oc2, oc3)}}
    """
    if not isinstance(PQ, TACQ):
        raise TypeError('The parapeter "PQ" must be a rewritten privacy TACQ !')
    if not isinstance(unionUQs, TACQ):
        raise TypeError('The parameter "UQs" must be the TACQ containing the union of Utility graph patterns !')

    # Freeze union of graph patterns
    freezing = unionUQs.freeze()

    ##############################
    vprint('-----------------------------')
    vprint('Freezing of the union of UQs:')
    vprint('-----------------------------')
    vprint(freezing.serialize(format="turtle"))
    ##############################

    if mainArgs.verbose:
        unionUQs.printConstants()
        print()

    # Execute PQ on the freezing
    query = 'PREFIX res:<http://example.org/>\n'
    query = query + 'SELECT ' + PQ.listGPVars(timestamps=False) + '\n'
    query = query + 'WHERE { '
    for p in PQ.gp:
        query = query + p['subject'] + ' '
        query = query + 'ns1' + p['predicate'] + ' '
        if p['object'][0] != '?':
            query = query + '"' + p['object'] + '" . '

        else:
            query = query + p['object'] + ' . '
    query = query[:-3] + ' }'

    ##############################
    vprint('--------------------------------------')
    vprint('Execution of rewrtitten privacy query:')
    vprint('--------------------------------------')
    vprint('Query:')
    vprint(query)
    vprint()
    ##############################

    result = freezing.query(query)

    vars = PQ.listGPVars(timestamps=False).split()
    if mainArgs.verbose:
        printQueryResults(result, vars)
        print()
    
    #
    # Check Theorem 4.1 and 4.3
    #

    compatible = True
    reasons = {}
    # for each line of the query result
    lineNb = 1
    for line in result:
        # suppose it is not compatible
        comp = False
        reason = {}
        # test output variables: if no full PQ result can be obtained => comptaible
        for v in range(len(vars)):
            if vars[v][1] == 'o' and line[v][0] != 'o':
                comp = True

        # test all join conditions
        if not(comp):
            res = []
            for (l,r) in PQ.joins:
                #left var
                il = vars.index(l)
                vl = line[il]
                # right var
                ir = vars.index(r)
                vr = line[ir]
                # test join: different value and one is not an output value => compatible
                if (vl[0] != 'o' or vr[0] != 'o') and (vl != vr):
                    comp = True
                elif not(comp) and vl != vr:
                    if not lineNb in reason.keys(): 
                        reason[lineNb] = [(vl, vr)]
                    elif not (vl, vr) in reason[lineNb]:
                        reason[lineNb].append((vl, vr))
            if not(comp):
                reasons.update(reason.copy())

        Reasons = []

        if not PQ.joins:
            Reasons.append(f"The freezing returns results for {PQ.prefix}")
        for r in reasons.keys():
            cond = ''
            for (v1, v2) in reasons[r]:
                cond = cond + f"{v1} == {v2} and "
            Reasons.append(f"A freezing where {cond[:-5]} returns results for {PQ.prefix} in line {str(r)}")

        # conclusion
        if not comp:
            compatible = False
        lineNb = lineNb + 1

    return {'compatible' : compatible, 'reasons' : Reasons, 'results' : result}

filterExp = ""


def condition(v1=0,  v2=0,  v3=0,  v4=0,  v5=0,  v6=0,  v7=0,  v8=0,  v9=0,  v10=0, 
              v11=0, v12=0, v13=0, v14=0, v15=0, v16=0, v17=0, v18=0, v19=0, v20=0, 
              v21=0, v22=0, v23=0, v24=0, v25=0, v26=0, v27=0, v28=0, v29=0, v30=0, 
              v31=0, v32=0, v33=0, v34=0, v35=0, v36=0, v37=0, v38=0, v39=0, v40=0, 
              v41=0, v42=0, v43=0, v44=0, v45=0, v46=0, v47=0, v48=0, v49=0, v50=0, 
              v51=0, v52=0, v53=0, v54=0, v55=0, v56=0, v57=0, v58=0, v59=0, v60=0, 
              v61=0, v62=0, v63=0, v64=0, v65=0, v66=0, v67=0, v68=0, v69=0, v70=0, 
              v71=0, v72=0, v73=0, v74=0, v75=0, v76=0, v77=0, v78=0, v79=0, v80=0, 
              v81=0, v82=0, v83=0, v84=0, v85=0, v86=0, v87=0, v88=0, v89=0, v90=0, 
              v91=0, v92=0, v93=0, v94=0, v95=0, v96=0, v97=0, v98=0, v99=0, v100=0):
    """
    Condition function for testing satisfiability
    """
    global filterExp
    return eval(filterExp)

def checkTheorem46(PQ, unionUQs, results):
    """
    Checks comptibility according to Theorem 4.6 (Filter)

    inputs: - PQ       -> a privacy query to check
            - unionUQs -> union of utility queries GP, Filters and Joins
            - results  -> result of PQ evaluated on a freezing of unionQUs
    output: -  a dictionnary { compatible, reasons } where:
                - compatible is a boolean
                - reasons is a list of result line numbers where filter satisfiability has been detected
    """

    global filterExp
    reasons = []

    # freeze unionQUs
    unionUQs.freeze()

    # compute union of PQ and UQs (GPs, filters and joins)
    bigQ = PQ.union(unionUQs)

    ##############################
    if mainArgs.verbose:
        print("-------------------------")
        print("bigQ : union of PQ an UQs")
        print("-------------------------")
        print(bigQ.toString())
        print()
        print("-------------")
        print("biQ Constants")
        print("-------------")
        bigQ.printConstants()
        print()
    ##############################

    compatible = True
    lnb = 0
    vars = PQ.listGPVars(timestamps=False).split()

    #
    # for each line in the result, test filter satisfiability
    #

    for line in results:
        lnb = lnb + 1

        ##############################
        if mainArgs.verbose:
            print("---------------")
            print(f"Result line {lnb}")
            print("---------------")
            for r in range(len(line)):
                print(vars[r], "=", line[r])
            print()
        ##############################

        filterExp = ""
        problem = Problem()

        # work on Q, a copy of bigQ
        Q = bigQ.copy()
         
        # parse given result to build overlap

        ## build variable correspondance
        Q.variables = {}

        ### for each var in PQ GP
        for v in range(len(vars)):
            # get corresponding constant un result line
            cst = str(line[v])

            # find corresponding variable name in UQs
            for (i,j) in Q.constants.items():
                if j == cst:
                    # rename PQ variable in Q
                   Q.variables[vars[v]] = i
        
        ##############################
        if mainArgs.verbose:
            print("--------------------")
            print("Renamed PQ variables")
            print("--------------------")
            Q.printVariables()
            print()
        ##############################

        ## rename variables in filter
        for f in range(len(Q.filter)):
            try:
                opl = Q.variables[str(Q.filter[f]['opl'])]
            except KeyError:
                opl = Q.filter[f]['opl']
            comp = Q.filter[f]['comp']
            try:
                opr = Q.variables[str(Q.filter[f]['opr'])]
            except KeyError:
                opr = Q.filter[f]['opr']
            Q.filter[f] = {'opl' : opl, 'comp' : comp, 'opr' : opr}

        ## rename variables in joins
        toDel = []
        for n in range(len(Q.joins)):
            (i,j) = Q.joins[n]
            try:
                i = Q.variables[i]
            except KeyError:
                pass
            try:
                j = Q.variables[j]
            except KeyError:
                pass
            if not (i,j) in Q.joins and i != j:
                Q.joins[n] = (i,j)
            else:
                toDel.append(n)
        for n in reversed(toDel):
            del Q.joins[n]


        ##############################
        if mainArgs.verbose:
            print("----------------")
            print("Rewritten filter")
            print("----------------")
            print(Q.toString("fj")[:-2])
            print()
        ##############################
        
        # set types for UQ variables
        Q.typeVars()

        ##############################
        if mainArgs.verbose:
            print("----------------")
            print("Q Variable Types")
            print("----------------")
            Q.printVarTypes()
            print()
        ##############################

        ## prepare variable domains generation
        intVars = []
        strVars = []
        floatVars = []
        dateVars = []
        unknownVars = []

        intConst = []
        strConst = []
        floatConst = []
        dateConst = []

        ## list variables and constants by type in filter
        for f in Q.filter:
            # opl is a variable
            if isinstance(f['opl'], str) and f['opl'][0] == '?':
                if str(Q.varTypes[f['opl']]) == "<class 'int'>":
                    intVars.append(f['opl'])
                if str(Q.varTypes[f['opl']]) == "<class 'str'>":
                    strVars.append(f['opl'])
                if str(Q.varTypes[f['opl']]) == "<class 'float'>":
                    floatVars.append(f['opl'])
                if str(Q.varTypes[f['opl']]) == "<class 'datetime.datetime'>" or str(Q.varTypes[f['opl']]) == "<class 'datetime'>":
                    dateVars.append(f['opl'])
                if str(Q.varTypes[f['opl']]) == 'unknown':
                    unknownVars.append(f['opl'])
            
            # opl is a constant
            else:
                if isinstance(f['opl'], int):
                    intConst.append(f['opl'])
                elif isinstance(f['opl'], str):
                    strConst.append(f['opl'])
                elif isinstance(f['opl'], float):
                    floatConst.append(f['opl'])
                elif isinstance(f['opl'], datetime):
                    dateConst.append(f['opl'])

            # opr is a variable
            if isinstance(f['opr'], str) and f['opr'][0] == '?':
                if str(Q.varTypes[f['opr']]) == "<class 'int'>":
                    intVars.append(f['opr'])
                if str(Q.varTypes[f['opr']]) == "<class 'str'>":
                    strVars.append(f['opr'])
                if str(Q.varTypes[f['opr']]) == "<class 'float'>":
                    floatVars.append(f['opr'])
                if str(Q.varTypes[f['opl']]) == "<class 'datetime.datetime'>" or str(Q.varTypes[f['opl']]) == "<class 'datetime'>":
                    dateVars.append(f['opr'])
                if str(Q.varTypes[f['opr']]) == 'unknown':
                    unknownVars.append(f['opr'])

            # opr is a constant
            else:
                if isinstance(f['opr'], int):
                    intConst.append(f['opr'])
                elif isinstance(f['opr'], str):
                    strConst.append(f['opr'])
                elif isinstance(f['opr'], float):
                    floatConst.append(f['opr'])
                elif isinstance(f['opr'], datetime):
                    dateConst.append(f['opr'])


        # list variables by type in joins
        for n in range(len(Q.joins)):
            (i, j) = Q.joins[n]
            # Left variable i
            if str(Q.varTypes[i]) == "<class 'int'>":
                intVars.append(i)
            elif str(Q.varTypes[i]) == "<class 'str'>":
                strVars.append(i)
            elif str(Q.varTypes[i]) == "<class 'float'>":
                floatVars.append(i)
            elif str(Q.varTypes[i]) == "<class 'datetime.datetime'>" or str(Q.varTypes[i]) == "<class 'datetime'>":
                dateVars.append(i)
            else:
                unknownVars.append(i)

            # right variable j
            if str(Q.varTypes[j]) == "<class 'int'>":
                intVars.append(j)
            elif str(Q.varTypes[j]) == "<class 'str'>":
                strVars.append(j)
            elif str(Q.varTypes[j]) == "<class 'float'>":
                floatVars.append(j)
            elif str(Q.varTypes[i]) == "<class 'datetime.datetime'>" or str(Q.varTypes[i]) == "<class 'datetime'>":
                dateVars.append(j)
            else:
                unknownVars.append(j)


        # elimiate duplicates in lists and sort them
        intVars = list(set(intVars))
        strVars = list(set(strVars))
        floatVars = list(set(floatVars))
        dateVars = list(set(dateVars))
        unknownVars = list(set(unknownVars))

        intConst = sorted(list(set(intConst)))
        strConst = sorted(list(set(strConst)))
        floatConst = sorted(list(set(floatConst)))
        dateConst = sorted(list(set(dateConst)))


        # generate domains for constants and variables 
        intDomain = []
        strDomain = []
        floatDomain = []
        dateDomain = []
        unknownDomain = []
        constants = {}

        end = 0
        begin = end

        ## integer
        pos = begin
        for i in intConst:
            constants[i] = pos + len(intVars)
            pos = pos + len(intVars) + 1
        if pos != begin:
            end = pos + len(intVars) - 1
            intDomain = range(begin, end)
            begin = end + 1

        ## str
        pos = begin
        for i in strConst:
            constants[i] = pos + len(strVars)
            pos = pos + len(strVars) + 1
        if pos != begin:
            end = pos + len(strVars) - 1
            strDomain = range(begin, end)
            begin = end + 1

        ## float
        pos = begin
        for i in floatConst:
            constants[i] = pos + len(floatVars)
            pos = pos + len(floatVars) + 1
        if pos != begin:
            end = pos + len(floatVars) - 1
            floatDomain = range(begin, end)
            begin = end + 1

        ## date
        pos = begin
        for i in dateConst:
            constants[i] = pos + len(dateVars)
            pos = pos + len(dateVars) + 1
        if pos != begin:
            end = pos + len(dateVars) - 1
            dateDomain = range(begin, end)
            begin = end + 1

        ## unknown variables
        pos = begin
        end = begin + 2*len(unknownVars) + 1
        unknownDomain = range(begin, end)

        ##############################
        if mainArgs.verbose:
            print("------------------")
            print("Constants encoding")
            print("------------------")
            for (i,j) in constants.items():
                print(i, "->", j)
            print()

            print("---------------------")
            print("Variables and domains")
            print("---------------------")
            if intVars:
                print("int variables    :", intVars)
                print("    domain       :", intDomain)
            if strVars:
                print("str variables    :", strVars)
                print("    domain       :", strDomain)
            if floatVars:
                print("float variables  :", floatVars)
                print("      domain     :", floatDomain)
            if dateVars:
                print("date variables   :", dateVars)
                print("     domain      :", dateDomain)
            if unknownVars:
                print("unknown variables:", unknownVars)
                print("        domain   :", unknownDomain)
            print()
        ##############################


        # generate filter expression
        for f in Q.filter:
            if f['comp'] == '=':
                comp = '=='
            else:
                comp = f['comp']

            if str(f['opl'])[0] == '?':
                opl = f['opl']
            else:
                opl = constants[f['opl']]

            if str(f['opr'])[0] == '?':
                opr = f['opr']
            else:
                opr = constants[f['opr']]
            filterExp = filterExp + f"{str(opl)} {comp} {str(opr)} and "
        for (i,j) in Q.joins:
            if i != j:
                filterExp = filterExp + f"{i} == {j} and "
        filterExp = filterExp[:-5]


        # rename variables in filter expression
        filterVariables = {}

        n = 1
        exp = filterExp.split()

        ##############################
        vprint("------------------------------")
        vprint("Expression to be tested by CSP")
        vprint("------------------------------")
        ##############################

        for pos in range(len(exp)):
            if exp[pos][0] == '?':
                var = ''
                for (i,j) in filterVariables.items():
                    if j == exp[pos]:
                        exp[pos] = i
                        var = i
                if var == '':
                    var = f"v{n}"
                    filterVariables[var] = str(exp[pos])
                    exp[pos] = var
                    n = n + 1

        
        # test filter
        ## int variables
        for v in intVars:
            var = v
            for (i,j) in Q.variables.items():
                if i == v:
                    var = j
            for (i,j) in filterVariables.items():
                if j == var:
                    try:
                        problem.addVariable(i, intDomain)
                        ##############################
                        vprint(i, "int :", intDomain)
                        ##############################
                    except ValueError:
                        pass

        ## str variables
        for v in strVars:
            var = v
            for (i,j) in Q.variables.items():
                if i == v:
                    var = j
            for (i,j) in filterVariables.items():
                if j == var:
                    try:
                        problem.addVariable(i, strDomain)
                        ##############################
                        vprint(i, "str :", strDomain)
                        ##############################
                    except ValueError:
                        pass

        ## float variables
        for v in floatVars:
            var = v
            for (i,j) in Q.variables.items():
                if i == v:
                    var = j
            for (i,j) in filterVariables.items():
                if j == var:
                    try:
                        problem.addVariable(i, floatDomain)
                        ##############################
                        vprint(i, "float :", floatDomain)
                        ##############################
                    except ValueError:
                        pass

        ## date variables
        for v in dateVars:
            var = v
            for (i,j) in Q.variables.items():
                if i == v:
                    var = j
            for (i,j) in filterVariables.items():
                if j == var:
                    try:
                        problem.addVariable(i, dateDomain)
                        ##############################
                        vprint(i, "date :", dateDomain)
                        ##############################
                    except ValueError:
                        pass

        ## unknown variables
        for v in unknownVars:
            var = v
            for (i,j) in Q.variables.items():
                if i == v:
                    var = j
            for (i,j) in filterVariables.items():
                if j == var:
                    try:
                        problem.addVariable(i, unknownDomain)
                        ##############################
                        vprint(i, "unknown :", unknownDomain)
                        ##############################
                    except ValueError:
                        pass

        filterExp = ''
        for i in exp:
            filterExp = filterExp + i + ' '

        ##############################
        vprint()
        vprint('   ', filterExp)
        vprint()
        ##############################


        # Test sisfiability
        problem.addConstraint(condition, list(filterVariables.keys()))
        res = problem.getSolution()

        ##############################
        vprint("-----------")
        vprint("Test result")
        vprint("-----------")
        vprint(res)
        vprint()
        ##############################

        if res:
            compatible = False
            reasons.append(lnb)

    return {'compatible' : compatible, 'reasons' : reasons}



def printQueryResults(results, vars):
    """
    Prints the result of q SAPRQL query (RDFlib)

    inputs: - results -> query results
            - vars    -> list of var names
    output: - None
    """
    if not isinstance(vars, list):
        raise TypeError('The parameter "vars" of printQueryResults() must be a list of var names !')

    # size of line numbers
    lnb = len(str(len(results)))
        
    # size of var names
    lv = [len(v) for v in vars]

    # header
    header1 = '+-' + '-'*lnb + '-+-'
    header2 = '| ' + f"{'#':{lnb}}" + ' | '
    for v in range(len(vars)):
        header1 = header1 + '-' * lv[v] + '-+-'
        header2 = header2 + f"{vars[v]:{lv[v]}}" +' | '
    print(header1[:-1])
    print(header2[:-1])
    print(header1[:-1])

    # content
    nb = 1
    for res in results:
        line = '| ' + f"{nb:{lnb}}" + ' | '
        for v in range(len(vars)):
            line = line + f"{res[v]:{lv[v]}}" + ' | '
        print(line[:-1])
        nb = nb +1
    print(header1[:-1])



def get_cmd_line_args():
    """
    Parse the command line to get parameters.
    
    input:  - none
    output: - a Namespace containing parameter values
    """
    parser = argparse.ArgumentParser()
    parser.add_argument('-p', '--privacy', help = 'file containing the privacy queries', default = 'privacy.sparql')
    parser.add_argument('-u', '--utility', help = 'file containing the utility queries', default = 'utility.sparql')
    parser.add_argument('-v', '--verbose', help = 'details each step', action="store_true")
    return parser.parse_args()



def vprint(*args):
    """
    Prints arguments if Verbose is on.

    inputs: - something to print
    output: - None
    """
    if mainArgs.verbose:
        for i in list(args):
            print(str(i), end=" ")
        print()

    
mainArgs = get_cmd_line_args()

def main():
    # Arguments
    
    ##############################
    vprint('----------')
    vprint('Arguments:')
    vprint('----------')
    vprint('Privacy file:', mainArgs.privacy)
    vprint('Utility file:', mainArgs.utility)
    vprint('Verbose is on.')
    vprint()
    ##############################

    # Privacy queries
    PQs = readTACQs(mainArgs.privacy, 'PQ')

    ##############################
    vprint('----------------')
    vprint('Privacy queries:')
    vprint('----------------')
    for q in PQs.keys():
        vprint(q, ':')
        vprint(PQs[q].toString())
        vprint()
    ##############################

    # Rename variables and extract joins from privacy queries
    for q in PQs.keys():
        PQs[q].renameVariables(prefix=q)
        PQs[q].extractJoins()
    
    ##############################
    vprint('--------------------------')
    vprint('Rewritten privacy queries:')
    vprint('--------------------------')
    for q in PQs.keys():
        vprint(q, ':')
        vprint(PQs[q].toString())
        if mainArgs.verbose:
            PQs[q].printVariables()
        vprint()
    ##############################

    # Reify privacy queries

    ##############################
    vprint('------------------------')
    vprint('Reified privacy queries:')
    vprint('------------------------')
    ##############################

    for q in PQs.keys():
        PQs[q].reify()

    ##############################
    for q in PQs.keys():
        vprint(q, ':')
        vprint(PQs[q].toString())
        vprint()
    ##############################
    
    # Utility queries
    UQs = readTACQs(mainArgs.utility, 'UQ')

    ##############################
    vprint('----------------')
    vprint('Utility queries:')
    vprint('----------------')
    for q in UQs.keys():
        vprint(q, ':')
        vprint(UQs[q].toString())
        vprint()
    ##############################

    # Rename variables of utility queries
    for q in UQs.keys():
        UQs[q].renameVariables(prefix=q)
  
    ##############################
    vprint('--------------------------')
    vprint('Rewritten utility queries:')
    vprint('--------------------------')
    for q in UQs.keys():
        vprint(q, ':')
        vprint(UQs[q].toString())
        if mainArgs.verbose:
            UQs[q].printVariables()
        vprint()
    ##############################

    # Reify utility queries
    for q in UQs.keys():
        UQs[q].reify()

    ##############################
    vprint('------------------------')
    vprint('Reified utility queries:')
    vprint('------------------------')
    for q in UQs.keys():
        vprint(q, ':')
        vprint(UQs[q].toString())
        vprint()
    ##############################


    # Compute union of utility query graph patterns
    unionUQs = TACQ()
    for q in UQs.keys():
        unionUQs = unionUQs.union(UQs[q])

    ##############################
    vprint('------------------------')
    vprint('Union of graph patterns:')
    vprint('------------------------')
    vprint(unionUQs.toString('wj')[8:-2])
    vprint()
    ##############################

    # For each pricavy query
    compatibility = 'True'
    for q in PQs.keys():
        comp = 'True'
        ##############################
        vprint()
        vprint('-'*len(q))
        vprint(q)
        vprint('-'*len(q))
        vprint()
        ##############################

        # Check Theorems 4.1 and 4.3

        ##############################
        vprint()
        vprint('=========================')
        vprint('Check Theorems 4.1 or 4.3')
        vprint('=========================')
        vprint()
        ##############################

        res = checkTheorem41(PQs[q], unionUQs)

        if res['compatible']:
            vprint(f"According to Theorem 4.3, privacy query {q} is compatible with the utility policy.")
        else:
            # conjunctive query => full characterization
            if PQs[q].isConjunctive():
                ##############################
                vprint(f"According to Theorem 4.1 (full characterization), privacy query {q} IS NOT COMPATIBLE with utility policy !")
                ##############################
                comp = 'False'
            # TACQ => sufficient condition
            else:
                ##############################
                vprint(f"According to Theorem 4.3 (sufficient condition), privacy query {q} MAY NOT BE COMPATIBLE with utility policy !")
                ##############################
                if comp != 'False':
                    comp = 'Maybe'
            ##############################
            vprint('Reason(s):')
            for r in res['reasons']:
                vprint(r)
            ##############################

        ##############################
        vprint()
        ##############################

        # Check Theorem 4.5 and 4.6
        if comp == 'Maybe':
            comp = 'True'

            ##############################
            vprint()
            vprint('=========================')
            vprint('Check Theorems 4.5 or 4.6')
            vprint('=========================')
            vprint()
            ##############################

            res = checkTheorem46(PQs[q], unionUQs, res['results'])
            if res['compatible']:
                ##############################
                vprint(f"According to Theorem 4.6 (sufficient condition), privacy query {q} is compatible with utility policy ! ")
                ##############################
            else:
                if PQs[q].aggregate:
                    ##############################
                    vprint(f"According to Theorem 4.6 (sufficient condition), privacy query {q} MAY NOT BE COMPATIBLE with utility policy !")
                    vprint("Aggregate functions and time windows have to be checked...")
                    ##############################
                    if comp != 'False':
                        comp = 'Maybe'
                else:
                    ##############################
                    vprint(f"According to Theorem 4.5, privacy query {q}, containing no aggregate computation, IS WEAKLY INCOMPATIBLE with utility policy !")
                    ##############################
                    comp = 'False'
                
                ##############################
                vprint()
                vprint("Reason(s):")
                line = ''
                for n in res['reasons']:
                    line = line + str(n) +", "
                vprint("The filter expression is satisfiable for result line(s)", line[:-2])
                vprint()
                ##############################
        if comp == 'Maybe':
            compatibility = 'Maybe'
        if comp == 'False':
            compatibility = 'False'

    # Conclusion
    vprint()
    vprint('===========')
    vprint('Conclusion:')
    vprint('===========')
    if compatibility == 'True':
        print('Privacy and utility Policies are compatible.')
    elif compatibility == 'Maybe':
        print('Privacy and utility policies MAY NOT BE COMPATIBLE !')
    else:
        print('Privacy and utility policies ARE NOT COMPATIBLE !')

    print()
        

if __name__ == '__main__':
    main()
