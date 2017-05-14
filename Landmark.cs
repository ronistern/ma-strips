using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Planning
{
    
    
    class Landmark
    {
       public string type;
       public bool GoalLandmark { get;  set; }
       public bool secondRound=false;
       public List<GroundedPredicate> publicEffects;
       public Landmark myMuster = null;
       public Dictionary<GroundedPredicate, string> facts = null;
       public int worth = 1;
       public int depth = 0;
       public int code = -1;
       public int index=-1;
       public bool AchieversPossibleInTheInitial = false;
       public bool isPublic = false;
       public bool mix = false;
       public List<Action> lAchievers = null; 
        public Landmark(string type1, bool bGoalLandmark)
        {
            type = type1;
            facts = new Dictionary<GroundedPredicate, string>();
            GoalLandmark = bGoalLandmark;
        }

        public void AddFact(GroundedPredicate gp, string s)
        {
            facts[gp] = s;
        }
        public void AddPublicFact(GroundedPredicate gp, string s)
        {
            if (facts.Count == 0)
            {
                isPublic = true;
                mix = false;
            }
            else
            {
                if (!isPublic)
                    mix = true;
            }

            if (!facts.ContainsKey(gp))
            {
                facts.Add(gp,s);
            }
        }
        public void AddPrivateFact(GroundedPredicate gp, string s)
        {
            if (facts.Count == 0)
            {
                isPublic = false;
                mix = false;
            }
            else
            {
                if (isPublic)
                {
                    isPublic = false;
                    mix = true;
                }
            }

            if (!facts.ContainsKey(gp))
            {
                facts.Add(gp, s);
            }
  
        }
        public bool Equals(Landmark p2)
        {
            if (Object.ReferenceEquals(this, p2))
                return true;
            if (null == p2)
                return false;
            if (this.index == p2.index)
                return true;
            return false;

            foreach (GroundedPredicate fact in p2.facts.Keys)
            {
                if (!this.facts.ContainsKey(fact))
                    return false;
            }
            foreach (GroundedPredicate fact in this.facts.Keys)
            {
                if (!p2.facts.ContainsKey(fact))
                    return false;
            }

            return true;
        }
        public bool Identical(Landmark p2)
        {
            if (Object.ReferenceEquals(this, p2))
                return true;
            if (null == p2)
                return false;
            

            foreach (GroundedPredicate fact in p2.facts.Keys)
            {
                if (!this.facts.ContainsKey(fact))
                    return false;
            }
            foreach (GroundedPredicate fact in this.facts.Keys)
            {
                if (!p2.facts.ContainsKey(fact))
                    return false;
            }

            return true;
        }
        public override bool Equals(object obj)
        {
            if (obj is Landmark)
                return Equals((Landmark)obj);
            return false;
        }
        public bool Belongs(PrivacyPreservingLandmark ppl)
        {
            if (ppl.index == index)
                return true;
            return false;
        }
        public override string ToString()
        {
            string str = "";
            foreach (var fact in facts.Keys)
            {
                str += fact.ToString() + " Or ";
            }
            str=str.Remove(str.Length - 4);
            return str;
        }

        public override int GetHashCode()
        {
            if (code == -1)
                code = ToString().GetHashCode();
            return code;
        }
        public static bool Comparer(Landmark x, Landmark y)
        {
            if (x.Identical(y))
                return true;
            return false;
        }
    }
    class LandmarkEqualityComparer : IEqualityComparer<Landmark>
    {

        public bool Equals(Landmark l1, Landmark l2)
        {
            if(l1.Identical(l2))
            {
                return true;
            }
            else
            {
                return false;
            }
        }


        public int GetHashCode(Landmark l)
        {
            string str="";
            foreach (GroundedPredicate gp in l.facts.Keys)
                str += gp.ToString();
            return str.GetHashCode();
        }

    }
}
