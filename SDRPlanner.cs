using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using System.IO;
using System.Threading;

namespace Planning
{
    class SDRPlanner
    {

        HashSet<GroundedPredicate>[] states;
        HarderProblemsAlg h = null;
        public static bool SDR_OBS { set; get; }

        public enum Planners { FF, FFsa, FFha, MIPS, MetricFF, LPG, FD }
        public enum Translations { SDR, MPSR }

        private static Dictionary<Thread, Process> FFProcesses = new Dictionary<Thread, Process>();

        public static Planners Planner = Planners.FF;
        public static Translations Translation = Translations.SDR;

        public ExecutionData Data{get; private set;}


        public static TimeSpan PlannerTimeout = new TimeSpan(0, 20, 0);
        public static bool WriteAllKVariations = false;
        public static bool ConsiderStateNegations = false;
        public static bool SplitConditionalEffects = false;
        public static bool RemoveAllKnowledge = true;
        public static bool ForceTagObservations = false;
        public static bool EnforceCNF = false;

        public static bool AddAllKnownToGiven { get; set; }
        public static bool AddTagRefutationToGoal { get; set; }

        public static List<string> SimulationStartState { get; set; }

        public static int TagsCount { get; set; }

        public SDRPlanner(string sPath, Domain d, Problem p)
        {
            Data = new ExecutionData(sPath, d, p);
        }
       

        private List<string> ChooseMaximumLengthPrefix(List<List<string>> lPlans)
        {
            List<List<string>> lCandidates = new List<List<string>>();
            foreach (List<string> lPlan in lPlans)
            {
                List<string> lClean = new List<string>();
                foreach (string sAction in lPlan)
                {
                    if (!sAction.StartsWith("merge") && !sAction.StartsWith("refute"))
                        lClean.Add(sAction);
                }
                lCandidates.Add(lClean);
            }
            int iCurrentAction = 0;
            while (lCandidates.Count > 1)
            {
                Dictionary<string, List<List<string>>> dActions = new Dictionary<string, List<List<string>>>();
                string sBestAction = "";
                foreach (List<string> lPlan in lCandidates)
                {

                    string sAction = "";
                    if(iCurrentAction < lPlan.Count)
                        sAction = lPlan[iCurrentAction];
                    if (!dActions.ContainsKey(sAction))
                        dActions[sAction] = new List<List<string>>();
                    dActions[sAction].Add(lPlan);
                    if (sBestAction == "" || dActions[sBestAction].Count < dActions[sAction].Count)
                        sBestAction = sAction;
                }
                if (sBestAction == "")
                    break;
                lCandidates = dActions[sBestAction];
                iCurrentAction++;
            }
            return lCandidates.First();
        }

       

        



        private List<string> ReadPlan(string sPath)
        {
            List<string> lPlan = new List<string>();
            string sPlanFile = "plan.txt";
            if (File.Exists(sPath + sPlanFile))
            {
                StreamReader sr = new StreamReader(sPath + sPlanFile);
                while (!sr.EndOfStream)
                {
                    string sAction = sr.ReadLine().Trim().ToLower();
                    if(sAction != "")
                        lPlan.Add(sAction);
                }
                sr.Close();
            }
            else if (File.Exists(sPath + "mipsSolution.soln"))
            {
                StreamReader sr = new StreamReader(sPath + "mipsSolution.soln");
                while (!sr.EndOfStream)
                {
                    string sLine = sr.ReadLine().Trim().ToLower();
                    if (sLine.Count() > 0 && !sLine.StartsWith(";"))
                    {
                        int iStart = sLine.IndexOf("(");
                        int iEnd = sLine.IndexOf(")");
                        sLine = sLine.Substring(iStart + 1, iEnd - iStart - 1).Trim();
                        lPlan.Add(sLine);
                    }
                }
                sr.Close();
            }
            else if (File.Exists(sPath + "sas_plan"))
            {
                StreamReader sr = new StreamReader(sPath + "sas_plan");
                while (!sr.EndOfStream)
                {
                    string sLine = sr.ReadLine().Trim().ToLower();
                    sLine = sLine.Replace("(", "");
                    sLine = sLine.Replace(")", "");
                    if (sLine.Count() > 0 && !sLine.StartsWith(";") )
                    {
                        int iStart = sLine.IndexOf("(");
                        sLine = sLine.Substring(iStart + 1).Trim();
                        lPlan.Add(sLine);
                    }
                }
                sr.Close();
            }
            else
            {
                /*
                if (SDRPlanner.AddTagRefutationToGoal)
                {
                    SDRPlanner.AddTagRefutationToGoal = false;
                    lPlan = Plan(sPath, pssCurrent, out sChosen);
                }
                else
                 * */

                //throw new Exception("ended");

                return null;
            }

            List<string> lFilteredPlan = new List<string>();
            foreach (string sAction in lPlan)
            {
                if (sAction.Contains("-remove") ||
                    sAction.Contains("-translate"))
                    continue;
                if (sAction.Contains("-add"))
                    lFilteredPlan.Add(sAction.Replace("-add", ""));
                else
                    lFilteredPlan.Add(sAction);

            }

            return lFilteredPlan;
        }

        static bool bFirst = true;

       

        private double ComputePlanSimilarity(List<string> lPlan1, List<string> lPlan2)
        {
            int i = 0;
            double cIntersection = 0;
            foreach (string sAction in lPlan1)
                if (lPlan2.Contains(sAction))
                    cIntersection++;
            return cIntersection / (lPlan1.Count + lPlan2.Count - cIntersection);
        }

        private double ComputePlanSimilarity(List<List<string>> lPlans)
        {
            double dMinSimilarity = 1.0;
            for (int i = 0; i < lPlans.Count - 1; i++)
            {
                for (int j = i + 1; j < lPlans.Count; j++)
                {
                    double dSim = ComputePlanSimilarity(lPlans[i], lPlans[j]);
                    if (dSim < dMinSimilarity)
                        dMinSimilarity = dSim;
                }
            }
            return dMinSimilarity;
        }
        
        private List<string> ComputeJointPrefix(List<List<string>> lPlans, Domain d)
        {
            List<string> lJointPrefix = new List<string>();
            List<List<string>> lPlansSuffix = new List<List<string>>();
            foreach (List<string> lPlan in lPlans)
                lPlansSuffix.Add(FilterReasoningActions(lPlan));
            string sCurrentAction = "";
            while (lPlansSuffix[0].Count > 0)
            {
                sCurrentAction = lPlansSuffix[0][0];
                bool bAllAgree = true;
                for (int i = 1; i < lPlansSuffix.Count; i++)
                {
                    if (lPlansSuffix[i][0] != sCurrentAction)
                        bAllAgree = false;
                }
                if (bAllAgree)
                {
                    lJointPrefix.Add(sCurrentAction);
                    foreach (List<string> lPlan in lPlansSuffix)
                        lPlan.RemoveAt(0);
                }
                else
                    break;
            }
            //now add all immediate sensing actions
            foreach (List<string> lPlan in lPlansSuffix)
            {
                int iCurrent = 0;
                while (d.IsObservationAction(lPlan[iCurrent]))
                {
                    if(!lJointPrefix.Contains(lPlan[iCurrent]))
                        lJointPrefix.Add(lPlan[iCurrent]);
                    iCurrent++;
                }
            }
            
            return lJointPrefix;
        }

        private List<string> ComputeSensingPrefix(List<List<string>> lPlans, Domain d)
        {
            List<string> lJointPrefix = new List<string>();
            List<List<string>> lPlansSuffix = new List<List<string>>();
            foreach (List<string> lPlan in lPlans)
                lPlansSuffix.Add(FilterReasoningActions(lPlan));
            SameAction sa = new SameAction();

            List<string> lFirstSensingPlan = null, lShortestPlan = null;
            int iFirstSensingAction = -1;
            int iAction = 0;
            int cPlans = lPlansSuffix.Count;
            for (iAction = 0; cPlans > 0 && lFirstSensingPlan == null; iAction++)
            {
                foreach (List<string> lPlan in lPlansSuffix)
                {
                    if (lPlan.Count == iAction)
                    {
                        if(lShortestPlan == null)
                            lShortestPlan = lPlan;
                        cPlans--;
                    }
                    if ( iAction < lPlan.Count && d.IsObservationAction(lPlan[iAction]))
                    {
                        iFirstSensingAction = iAction;
                        lFirstSensingPlan = lPlan;
                    }
                }
            }
            if (lFirstSensingPlan == null)
                lFirstSensingPlan = lShortestPlan;
            if (iFirstSensingAction == -1)
                iFirstSensingAction = lFirstSensingPlan.Count;


            for (iAction = 0; iAction < iFirstSensingAction; iAction++)
            {
                List<List<string>> lNewSuffixes = new List<List<string>>();
                foreach (List<string> lPlan in lPlansSuffix)
                {
                    if(sa.Equals(lPlan[iAction], lFirstSensingPlan[iAction]))
                        lNewSuffixes.Add(lPlan);
                }
                lJointPrefix.Add(lFirstSensingPlan[iAction]);
                lPlansSuffix = lNewSuffixes;
            }
            foreach (List<string> lPlan in lPlansSuffix)
            {
                for (iAction = iFirstSensingAction; iAction < lPlan.Count; iAction++)
                {
                    if (d.IsObservationAction(lPlan[iAction]))
                    {
                        if (!lJointPrefix.Contains(lPlan[iAction]))
                            lJointPrefix.Add(lPlan[iAction]);
                    }
                    else
                        break;
                }
            }
            
            return lJointPrefix;
        }

        private List<string> ComputeVotingPrefix(List<List<string>> lPlans, Domain d)
        {
            List<string> lJointPrefix = new List<string>();
            List<List<string>> lPlansSuffix = new List<List<string>>();
            foreach (List<string> lPlan in lPlans)
                lPlansSuffix.Add(FilterReasoningActions(lPlan));
            string sCurrentAction = "";
            SameAction sa = new SameAction();
            while (lPlansSuffix.Count >= lPlans.Count / 2 && lPlansSuffix[0].Count > 0)
            {
                bool bFoundObservationAction = false;
                Dictionary<string, int> dVotes = new Dictionary<string, int>(sa);
                foreach (List<string> lPlan in lPlansSuffix)
                {
                    if (lPlan.Count > 0)
                    {
                        while (d.IsObservationAction(lPlan[0]))
                        {
                            if (!lJointPrefix.Contains(lPlan[0]))
                            {
                                lJointPrefix.Add(lPlan[0]);
                            }
                            bFoundObservationAction = true;
                            lPlan.RemoveAt(0);
                        }
                        sCurrentAction = lPlan[0];
                        if (!dVotes.ContainsKey(sCurrentAction))
                            dVotes[sCurrentAction] = 0;
                        dVotes[sCurrentAction]++;
                    }
                }
                if (bFoundObservationAction)
                    break;
                string sMaxAction = dVotes.Keys.First();
                foreach (KeyValuePair<string, int> p in dVotes)
                {
                    if (p.Value > dVotes[sMaxAction])
                        sMaxAction = p.Key;
                }
                lJointPrefix.Add(sMaxAction);
                List<List<string>> lNewSuffixes = new List<List<string>>();
                foreach (List<string> lPlan in lPlansSuffix)
                {
                    if (lPlan.Count > 0 && sa.Equals(lPlan[0], sMaxAction))
                    {
                        lPlan.RemoveAt(0);
                        lNewSuffixes.Add(lPlan);
                    }
                }
                lPlansSuffix = lNewSuffixes;
            }
            return lJointPrefix;
        }

        private class SameAction : IEqualityComparer<string>
        {

            #region IEqualityComparer<string> Members

            public bool Equals(string s1, string s2)
            {
                int iTag1Index = s1.IndexOf("-kw-tag") + 7;
                string s1Tag = s1.Substring(iTag1Index, 1).Trim();
                s1 = s1.Replace("-kw-tag" + s1Tag, "");
                int iTag2Index = s2.IndexOf("-kw-tag") + 7;
                string s2Tag = s2.Substring(iTag2Index, 1).Trim();
                s2 = s2.Replace("-kw-tag" + s2Tag, "");
                return s1 == s2;
            }

            public int GetHashCode(string obj)
            {
                return obj.Substring(0, obj.IndexOf("-")).GetHashCode();
            }

            #endregion
        }

        private List<string> FilterReasoningActions(List<string> lPlan)
        {
            List<string> lFiltered = new List<string>();
            foreach (string sAction in lPlan)
            {
                if (sAction.StartsWith("merge") || sAction.StartsWith("unmerge") || sAction.StartsWith("tagrefute") || sAction.StartsWith("tagmerge") || sAction.StartsWith("refute"))
                    continue;
                if (sAction.EndsWith("-t") || sAction.EndsWith("-f"))
                    lFiltered.Add(sAction.Substring(sAction.Length - 2));
                else if (sAction.Contains("-t "))
                    lFiltered.Add(sAction.Replace("-t ", " "));
                else if (sAction.Contains("-f "))
                    lFiltered.Add(sAction.Replace("-f ", " "));
                else
                    lFiltered.Add(sAction);
            }
            return lFiltered;
        }

        private static void OutputHandler(object sendingProcess, DataReceivedEventArgs outLine)
        {
            //do nothing - not interested in the output
            //Debug.WriteLine(outLine.Data);
        }

       

        //static int iSeed = 0;
       
       

       

        //static int iSeed = 0;
      
        private bool IsReasoningAction(string sAction)
        {
            if (sAction.StartsWith("merge") || sAction.StartsWith("refute") || sAction.StartsWith("unmerge") || sAction.StartsWith("tagmerge"))
                return true;
            if (sAction.Contains("knowledgegain") || sAction.Contains("knowledgeloss"))
                return true;
            if (!sAction.StartsWith("r"))
                return false;
            for (int i = 1; i < sAction.Length; i++)
                if (sAction[i] < '0' || sAction[i] > '9')
                    return false;
            return true;
        }

   

        public void TerminateFFPRocesses(Thread t)
        {
            if (FFProcesses.ContainsKey(t))
            {
                if (FFProcesses[t] != null)
                {
                    FFProcesses[t].Kill();
                    FFProcesses[t].WaitForExit();
                }
                FFProcesses.Remove(t);
            }
        }

        public class ExecutionData
        {
            public int Observations { get; set; }
            public int Actions { get; set; }
            public int Planning { get; set; }
            public TimeSpan Time { get; set; }
            public Domain Domain { get; set; }
            public Problem Problem { get; set; }
            public string Path { get; set; }
            public string Exception { get; set; }
            public bool Failure { get { return Exception != ""; } }

            public ExecutionData(string sPath, Domain d, Problem p)
            {
                Domain = d;
                Problem = p;
                Path = sPath;
                Exception = "";
            }
            


        }



    }


}
