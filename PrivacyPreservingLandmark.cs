using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Planning
{
    class PrivacyPreservingLandmark
    {

        public static List<string> m_agents = new List<string>();
        public HashSet<string> achieversAgents = null;
        public string type;
        public bool isGoal = false;
        public bool toDevelop = true;
        public bool isPublic = true;
        public static int counter = 0;
        public Dictionary<string, List<Action>> lAchievers = new Dictionary<string, List<Action>>();
        Dictionary<string, Landmark> EncryptedLandmark = null;
        public int index;
        public PrivacyPreservingLandmark()
        {
            counter++;
            index = counter;
            EncryptedLandmark = new Dictionary<string, Landmark>();
            achieversAgents = new HashSet<string>();
            foreach (string ag in m_agents)
            {
                EncryptedLandmark.Add(ag, null);
                lAchievers.Add(ag, null);
            }

        }
        public void SetAchievers(string name, List<Action> lAchievers)
        {
            if (this.EncryptedLandmark[name] != null)
            {
                this.lAchievers[name] = lAchievers;
                this.EncryptedLandmark[name].lAchievers = lAchievers;
                achieversAgents.Add(name);
            }
        }

        public void AddPublicLandmark(Landmark l)
        {

            foreach (string ag in m_agents)
            {
                if (EncryptedLandmark[ag] == null)
                {
                    l.index = index;
                    EncryptedLandmark[ag] = new Landmark(l.type, l.GoalLandmark);
                }
                foreach (var fact in l.facts)
                {
                    if (!EncryptedLandmark[ag].facts.ContainsKey(fact.Key))
                    {
                        EncryptedLandmark[ag].AddFact(fact.Key, fact.Value);
                    }
                }

            }
        }
        public void SetIndex(int count)
        {
            index = count;
            foreach (string ag in m_agents)
            {
                if (EncryptedLandmark[ag] == null)
                {
                    EncryptedLandmark[ag] = new Landmark("FalseLandmark", false);
                    EncryptedLandmark[ag].GoalLandmark = isGoal;
                    EncryptedLandmark[ag].index = count;
                    EncryptedLandmark[ag].isPublic = isPublic;
                    EncryptedLandmark[ag].AddFact(new GroundedPredicate(Domain.FALSE_PREDICATE), "FalseLandmark");
                }
                else
                {
                    EncryptedLandmark[ag].index = count;
                    EncryptedLandmark[ag].GoalLandmark = isGoal;
                    EncryptedLandmark[ag].isPublic = isPublic;
                }
            }
        }
        public void AddPrivateLandmark(Landmark l, string name)
        {
            isPublic = false;
            if (EncryptedLandmark[name] == null)
            {
                l.index = index;
                EncryptedLandmark[name] = l;
            }
            else
            {
                foreach (var fact in l.facts)
                {
                    if (!EncryptedLandmark[name].facts.ContainsKey(fact.Key))
                    {
                        EncryptedLandmark[name].AddFact(fact.Key, fact.Value);
                    }
                }
            }
        }
        public void AddPublicPredicate(GroundedPredicate gp)
        {
            foreach (string ag in m_agents)
            {
                if (EncryptedLandmark[ag] == null)
                {
                    EncryptedLandmark[ag] = new Landmark("Disjunctive", false);
                    EncryptedLandmark[ag].AddFact(gp, "first_round");
                    EncryptedLandmark[ag].index = index;
                }
                else
                {

                    if (!EncryptedLandmark[ag].facts.ContainsKey(gp))
                    {
                        EncryptedLandmark[ag].AddFact(gp, "first_round");
                    }

                }
            }
        }

        public void AddPrivatePredicate(GroundedPredicate gp, string name)
        {
            isPublic = false;
            if (EncryptedLandmark[name] == null)
            {
                EncryptedLandmark[name] = new Landmark("Disjunctive", false);
                EncryptedLandmark[name].AddFact(gp, "first_round");
                EncryptedLandmark[name].index = index;
            }
            else
            {
                if (!EncryptedLandmark[name].facts.ContainsKey(gp))
                {
                    EncryptedLandmark[name].AddFact(gp, "first_round");
                }

            }
        }

        public Landmark GetAgentLandmark(string name)
        {
            return EncryptedLandmark[name];
        }

        public bool publishsingelOrder()
        {
            if (isPublic)
                return true;
            Landmark firstLandmark = EncryptedLandmark.ElementAt(0).Value;
            foreach (var item in EncryptedLandmark.Values)
            {
                if (firstLandmark.Identical(item))
                    return false;
            }
            return true;
        }

        public void Merge(PrivacyPreservingLandmark ppLandmark)
        {
            if (!ppLandmark.isPublic)
                isPublic = false;
            foreach (var item in ppLandmark.EncryptedLandmark)
            {
                if (item.Value != null)
                {
                    if (EncryptedLandmark[item.Key] == null)
                    {
                        EncryptedLandmark[item.Key] = item.Value;
                    }
                    else
                    {
                        // if (!isPublic)
                        //    isPublic = false;
                        string name = item.Key;
                        Landmark l = item.Value;
                        if (EncryptedLandmark[name] == null)
                        {
                            l.index = index;
                            EncryptedLandmark[name] = l;
                        }
                        else
                        {
                            foreach (var fact in l.facts)
                            {
                                if (!EncryptedLandmark[name].facts.ContainsKey(fact.Key))
                                {
                                    EncryptedLandmark[name].AddFact(fact.Key, fact.Value);
                                }
                            }
                        }
                    }
                }
            }
        }

        static public PrivacyPreservingLandmark MergeList(List<PrivacyPreservingLandmark> lPPLandmark)
        {
            PrivacyPreservingLandmark firstLandmark = lPPLandmark.ElementAt(0);
            for (int i = 1; i < lPPLandmark.Count; i++)
            {
                firstLandmark.Merge(lPPLandmark.ElementAt(i));
            }
            return firstLandmark;
        }

        public override bool Equals(object obj)
        {
            if (obj is PrivacyPreservingLandmark)
                return Equals((PrivacyPreservingLandmark)obj);
            return false;
        }

        public bool Equals(PrivacyPreservingLandmark l)
        {
            foreach (var item in EncryptedLandmark)
            {
                if (item.Value != null && l.EncryptedLandmark[item.Key] == null)
                    return false;
                if (item.Value == null && l.EncryptedLandmark[item.Key] != null)
                    return false;
                if (item.Value == null && l.EncryptedLandmark[item.Key] == null)
                    continue;
                if (!item.Value.Identical(l.EncryptedLandmark[item.Key]))
                    return false;
            }
            return true;
        }
        /* public override int GetHashCode()
         {
             return index;
         }*/
        public void RemoveAgent(string name)
        {
            EncryptedLandmark[name] = null;
        }
        public void TellAboutPublic(List<Agent> agents)
        {
            HashSet<GroundedPredicate> publicFacts = new HashSet<GroundedPredicate>();
            foreach (Agent agent in agents)
            {
                if (EncryptedLandmark[agent.name] != null)
                {
                    EncryptedLandmark[agent.name].isPublic = isPublic;
                    EncryptedLandmark[agent.name].index = index;
                    foreach (GroundedPredicate gp in EncryptedLandmark[agent.name].facts.Keys)
                    {
                        if (agent.PublicPredicates.Contains(gp))
                        {
                            publicFacts.Add(gp);
                        }
                    }
                }
            }
            foreach (Agent agent in agents)
            {
                foreach (GroundedPredicate gp in publicFacts)
                {
                    if (agent.PublicPredicates.Contains(gp))
                    {
                        if (EncryptedLandmark[agent.name] == null)
                        {
                            EncryptedLandmark[agent.name] = new Landmark("Disjunctive", false);
                            EncryptedLandmark[agent.name].AddFact(gp, "first_round");
                            EncryptedLandmark[agent.name].index = index;

                        }
                        else
                        {
                            if (!EncryptedLandmark[agent.name].facts.ContainsKey(gp))
                            {
                                EncryptedLandmark[agent.name].AddFact(gp, "first_round");
                            }

                        }

                    }
                    else
                    {
                        if (EncryptedLandmark[agent.name] != null && EncryptedLandmark[agent.name].facts.Keys.Contains(gp))
                        {
                            EncryptedLandmark[agent.name].facts.Remove(gp);
                            if (EncryptedLandmark[agent.name].facts.Count == 0)
                            {
                                EncryptedLandmark[agent.name] = null;
                            }
                        }
                    }
                }
            }
            List<Action> newlAchiever = new List<Action>();
            if (isPublic)
            {
                foreach (var lAction in this.lAchievers.Values)
                {
                    if (lAction != null)
                    {
                        newlAchiever.AddRange(lAction);
                    }
                }

                foreach (string name in m_agents)
                {
                    if (this.lAchievers[name] != null)
                    {
                        this.lAchievers[name] = newlAchiever;
                    }
                }
                foreach (string name in m_agents)
                {
                    if (this.EncryptedLandmark[name] != null)
                    {
                        this.EncryptedLandmark[name].lAchievers = newlAchiever;
                    }
                }
            }
        }
        public override string ToString()
        {
            string str = "";
            HashSet<GroundedPredicate> closeList = new HashSet<GroundedPredicate>();
            foreach (var item in EncryptedLandmark)
            {
                if (item.Value != null)
                {
                    foreach (var fact in item.Value.facts.Keys)
                    {

                        if (!closeList.Contains(fact) && !(fact.ToString().Contains(Domain.FALSE_PREDICATE)))
                        {
                            str += fact.ToString() + " Or ";
                            closeList.Add(fact);
                        }
                    }
                }
            }
            if (str == "") return "Empty";
            str = str.Remove(str.Length - 4);
            return str;
        }
        public static string Comparer(PrivacyPreservingLandmark ppl1, PrivacyPreservingLandmark ppl2)
        {
            List<GroundedPredicate> gp1List = new List<GroundedPredicate>();
            List<GroundedPredicate> gp2List = new List<GroundedPredicate>();
            if (ppl1.isPublic == false || ppl1.isPublic == false)
                return "Can't Comparer";
            foreach (string name in m_agents)
            {
                if (ppl1.EncryptedLandmark[name] != null)
                {
                    foreach (GroundedPredicate gp in ppl1.EncryptedLandmark[name].facts.Keys)
                    {
                        gp1List.Add(gp);
                    }
                }
                if (ppl2.EncryptedLandmark[name] != null)
                {
                    foreach (GroundedPredicate gp in ppl2.EncryptedLandmark[name].facts.Keys)
                    {
                        gp2List.Add(gp);
                    }
                }
            }
            bool identical = true;
            bool contain = false;
            foreach (GroundedPredicate gp in gp1List)
            {
                if (!gp2List.Contains(gp))
                {
                    identical = false;
                }
                else
                {
                    contain = true;
                }
            }
            foreach (GroundedPredicate gp in gp2List)
            {
                if (!gp1List.Contains(gp))
                {
                    identical = false;
                }
                else
                {
                    contain = true;
                }
            }
            if (identical)
                return "Identical";
            if (contain)
            {
                if (gp1List.Count < gp2List.Count)
                    return "First";
                else
                {
                    return "Second";
                }
            }
            return "Differents";


        }
    }

}
