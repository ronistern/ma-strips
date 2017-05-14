using System;
using System.Collections.Generic;

namespace Planning
{
    class MacroAction : Action
    {
        public static int counter = 1;
        //public Dictionary<string, bool[]> satNowVectors;
        //public Dictionary<string, bool[]> negSatNowVectors;
        public Dictionary<string, int> parentIndex;
        public Dictionary<string, int> childIndex;
        public List<string> preIndex = null;
        public int cost = 0;
        public int dellLandmarkCounter = 0;
        public List<string> lastpreIndex = null;
        public int heuristicDelta = 0;
        public bool[] landmarkVector = null;
        public bool[] NeglandmarkVector = null;
        public bool[] anyTimeVector = null;
        public bool[] rOrder = null;
        public List<Action> microActions = null;
        //public string name = "";

        /* public MacroAction()
             : base("MacroAction"+counter)
         {
             counter++;
         }*/

        public MacroAction(MapsVertex parentVertex, MapsVertex childVertex)
            : base("MacroAction" + counter)
        {
            // if (Name.Equals("MacroAction46"))
            //    Console.WriteLine("ss");
            lastpreIndex = new List<string>();
            preIndex = new List<string>();
            parentIndex = new Dictionary<string, int>(parentVertex.stateIndexes);
            childIndex = new Dictionary<string, int>(childVertex.stateIndexes);
            counter++;
            isPublic = false;
            Action lastPublicAction = childVertex.lplan[childVertex.lplan.Count - 1];
            //if (lastPublicAction == null)
            //    Console.WriteLine("ss");
            agent = lastPublicAction.agent;
            int k = 0;
            foreach (var indexItem in parentVertex.stateIndexes)
            {
                //parentIndex[k]=indexItem.Value;
                //childIndex[k] = childVertex.stateIndexes[indexItem.Key];
                if (!indexItem.Value.Equals(childVertex.stateIndexes[indexItem.Key]))
                {
                    lastpreIndex.Add(indexItem.Key);
                }
                k++;
            }
            cost = 0;
            microActions = new List<Action>();
            List<Action> pubActions = new List<Action>();
            for (int i = parentVertex.lplan.Count; i < childVertex.lplan.Count; i++)
            {
                microActions.Add(childVertex.lplan[i]);
                if (childVertex.lplan[i] is MacroAction)
                {
                    foreach (string a in ((MacroAction)childVertex.lplan[i]).preIndex)
                    {
                        if (!preIndex.Contains(a))
                            preIndex.Add(a);
                    }
                    cost += ((MacroAction)childVertex.lplan[i]).cost;
                }
                else
                {
                    if (!preIndex.Contains(childVertex.lplan[i].agent))
                        preIndex.Add(childVertex.lplan[i].agent);
                    cost += 1;
                }
                if (childVertex.lplan[i].isPublic || childVertex.lplan[i] is MacroAction)
                {
                    pubActions.Add(childVertex.lplan[i]);
                }
            }
   

            HashEffects = new List<Predicate>();
            HashPrecondition = new List<Predicate>();
            // if (parentVertex.isComplex)
            //   Console.WriteLine("**");
            foreach (Action pAct in pubActions)
            {
                foreach (GroundedPredicate pre in pAct.HashPrecondition)
                {
                    if (MapsPlanner.allPublicFacts.Contains(pre))
                    {
                        if (!HashEffects.Contains(pre) && !HashPrecondition.Contains(pre))
                            HashPrecondition.Add(pre);
                    }
                }
                foreach (GroundedPredicate eff in pAct.HashEffects)
                {
                    if (MapsPlanner.allPublicFacts.Contains(eff))
                    {

                        if (!HashEffects.Contains(eff))
                        {
                            if (HashEffects.Contains(eff.Negate()))
                                HashEffects.Remove(eff.Negate());

                            HashEffects.Add(eff);
                        }
                    }
                }
            }
            CompoundFormula prec = new CompoundFormula("and");
            foreach (GroundedPredicate precGp in HashPrecondition)
                prec.AddOperand(precGp);
            Preconditions = prec;

            CompoundFormula effe = new CompoundFormula("and");
            foreach (GroundedPredicate effeGp in HashEffects)
                effe.AddOperand(effeGp);
            Effects = effe;

            if (Program.highLevelPlanerType == Program.HighLevelPlanerType.MafsLandmark)
            {
                heuristicDelta = parentVertex.h - childVertex.h;
                landmarkVector = new bool[parentVertex.SatisfactionLandmarks.Length];
                NeglandmarkVector = new bool[parentVertex.SatisfactionLandmarks.Length];
                for (int i = 0; i < parentVertex.SatisfactionLandmarks.Length; i++)
                {
                    if (!parentVertex.SatisfactionLandmarks[i] && childVertex.SatisfactionLandmarks[i])
                    {
                        landmarkVector[i] = true;
                    }
                }
                for (int i = 0; i < parentVertex.SatisfactionLandmarks.Length; i++)
                {
                    if (parentVertex.SatisfactionLandmarks[i] && !childVertex.SatisfactionLandmarks[i])
                    {
                        NeglandmarkVector[i] = true;
                        dellLandmarkCounter++;
                    }
                }
                //if (microActions.Count > 1)
                //   Console.WriteLine("GnGaa");
                rOrder = new bool[parentVertex.vectors[agent][1].Length];
                foreach (string agnt in preIndex)
                {
                    for (int i = 0; i < parentVertex.vectors[agnt][1].Length; i++)
                    {
                        if (!parentVertex.vectors[agnt][1][i] && childVertex.vectors[agnt][1][i])
                        {
                            rOrder[i] = true;
                        }
                    }
                }
                anyTimeVector = new bool[parentVertex.anyTimeSatisfactionLandmarks.Length];
                for (int i = 0; i < parentVertex.SatisfactionLandmarks.Length; i++)
                {
                    if (!parentVertex.anyTimeSatisfactionLandmarks[i] && childVertex.anyTimeSatisfactionLandmarks[i])
                    {
                        anyTimeVector[i] = true;
                    }
                }

               
                /*satNowVectors = new Dictionary<string, bool[]>();
                negSatNowVectors=new Dictionary<string, bool[]>();
                foreach (string agnt in preIndex)
                {
                    satNowVectors.Add(agnt, new bool[childVertex.satisfiedVector[agnt].Length]);
                    negSatNowVectors.Add(agnt, new bool[childVertex.satisfiedVector[agnt].Length]);
                    for (int i = 0; i < childVertex.satisfiedVector[agnt].Length; i++)
                    {
                        if (childVertex.satisfiedVector[agnt][i] == true && parentVertex.satisfiedVector[agnt][i] == false)
                        {
                            satNowVectors[agnt][i] = true;
                        }
                        if (childVertex.satisfiedVector[agnt][i] == false && parentVertex.satisfiedVector[agnt][i] == true)
                        {
                            negSatNowVectors[agnt][i] = true;
                        }
                    }
                }*/
            }
        }
        public override bool Equals(object obj)
        {
            if (obj is MacroAction)
                return Equals((MacroAction)obj);
            return false;
        }
        int code = -1;
        public override int GetHashCode()
        {
            if (code != -1) return code;
            int fa = 0;
            int se = 0;
            foreach (string index in preIndex)
            {
                fa += parentIndex[index];
                se += childIndex[index];
            }
            code = (int)(Math.Pow(fa, se));
            return code;
        }
        public bool Equals(MacroAction a2)
        {
            if (this.preIndex.Count != a2.preIndex.Count)
                return false;
            if (HashPrecondition.Count != a2.HashPrecondition.Count)
                return false;
            if (HashEffects.Count != a2.HashEffects.Count)
                return false;

            foreach (var index in preIndex)
            {
                if (!a2.parentIndex[index].Equals(parentIndex[index]))
                    return false;
                if (!a2.childIndex[index].Equals(childIndex[index]))
                    return false;
            }

            foreach (GroundedPredicate gp in HashPrecondition)
            {
                if (!a2.HashPrecondition.Contains(gp))
                    return false;
            }
            foreach (GroundedPredicate gp in HashEffects)
            {
                if (!a2.HashEffects.Contains(gp))
                    return false;
            }
            return true;
        }

    }
}
