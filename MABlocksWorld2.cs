using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;

namespace Planning
{
    class MABlocksWorld2
    {
        public int Blocks { get; private set; }
        public int Arms { get; private set; }
        public int MaxStacksPerAgent { get; private set; }
        public List<List<int>> m_lAgentStacks;
        public List<int> m_lPublicStacks;
        private Stack<int>[] m_aStartState, m_aGoalState;
        public MABlocksWorld2(int cBlocks, int cArms, int cMaxStacksPerAgent)
        {
            Blocks = cBlocks;
            Arms = cArms;
            MaxStacksPerAgent = cMaxStacksPerAgent;

            int cStacks = AssignStacksToAgents();

            Stack<int>[] a = new Stack<int>[cStacks];//Arms * MaxStacksPerAgent];
            for (int i = 0; i < a.Length; i++)
                a[i] = new Stack<int>();
            for (int i = 0; i < Blocks; i++)
                a[0].Push(i);
            m_aStartState = Shuffle(a, 10000);
            m_aGoalState = Shuffle(m_aStartState, 10000);

        }

        //implements a two cycle map
        private int AssignStacksToAgents()
        {
            //first we create a cycle of all but one
            m_lAgentStacks = new List<List<int>>();
            int iCurrentStack = 0;
            bool bSmallAgent = false;
            List<int> lStacks = null;
            for (int i = 0; i < Arms - 1; i++)
            {
                double dRand = RandomGenerator.NextDouble();
                bSmallAgent = dRand < 0.0;

                int cStacks = 0;
                if (bSmallAgent)
                    cStacks = RandomGenerator.Next(2) + 3;
                else
                    cStacks = RandomGenerator.Next(MaxStacksPerAgent / 2 ) + MaxStacksPerAgent / 2 + 3;
                lStacks = new List<int>();
                for (int j = 0; j < cStacks; j++)
                {
                    lStacks.Add(iCurrentStack + j);
                }
                m_lAgentStacks.Add(lStacks);
                iCurrentStack += cStacks - 1;
            }
            m_lAgentStacks.Last().Add(0);
            int iConnectStack1 = RandomGenerator.Next(iCurrentStack / 2);
            int iConnectStack2 = RandomGenerator.Next(iCurrentStack / 2) + iCurrentStack / 2;

           
            //now we cut the cycle in half
            lStacks = new List<int>();
            lStacks.Add(iConnectStack1);
            lStacks.Add(iCurrentStack + 1);
            lStacks.Add(iConnectStack2);
            m_lAgentStacks.Add(lStacks);

            m_lPublicStacks = new List<int>();
            for (int iStack = 0; iStack < iCurrentStack + 1; iStack++)
            {
                int cReachingArms = 0;
                foreach (List<int> l in m_lAgentStacks)
                {
                    if (l.Contains(iStack))
                        cReachingArms++;
                }
                if (cReachingArms > 1)
                    m_lPublicStacks.Add(iStack);
            }


            return (iCurrentStack + 2);
        }

        private Stack<int>[] Shuffle(Stack<int>[] a, int cMoves)
        {
            Stack<int>[] aShuffled = new Stack<int>[a.Length];
            for (int i = 0; i < a.Length; i++)
                aShuffled[i] = new Stack<int>(a[i]);

            for (int i = 0; i < cMoves; i++)
            {
                int iStack = RandomGenerator.Next(aShuffled.Length);
                if (aShuffled[iStack].Count == 0)
                    continue;
                int iTargetStack = -1;
                if (iStack == 0 || (iStack < a.Length - 1 && RandomGenerator.NextDouble() < 0.5))
                {
                    iTargetStack = iStack + 1;
                }
                else
                {
                    iTargetStack = iStack - 1;
                }

                int iBlock = aShuffled[iStack].Pop();
                aShuffled[iTargetStack].Push(iBlock);
            }
            return aShuffled;
        }

        public void WriteProblem(string sPathName)
        {
            StreamWriter sw = new StreamWriter(sPathName + @"\p.pddl");
            sw.WriteLine(GenerateProblem());
            sw.Close();
        }

        public void WriteFactoredProblems(string sPathName)
        {
            for (int iArm = 0; iArm < Arms; iArm++)
            {
                StreamWriter sw = new StreamWriter(sPathName + @"\problem-arm" + iArm + ".pddl");
                sw.WriteLine(GenerateFactoredProblem(iArm));
                sw.Close();
            }
        }

        private string GenerateFactoredProblem(int iArm)
        {
            string sProblem = "(define \n";
            sProblem += "(problem " + Name + "-arm" + iArm + ")\n";
            sProblem += "(:domain " + Name + "-arm" + iArm + ")\n";
            //sProblem += GenerateObjects(iArm) + "\n";
            sProblem += "(:init\n" + ToPartialState(m_aStartState, iArm, false) + ")\n";
            sProblem += "(:goal (and\n" + ToPartialState(m_aGoalState, iArm, true) + "))\n";
            sProblem += ")";
            return sProblem;
        }

        private string GenerateProblem()
        {
            string sProblem = "(define \n";
            sProblem += "(problem " + Name + ")\n";
            sProblem += "(:domain " + Name + ")\n";
            //sProblem += GenerateObjects() + "\n";
            sProblem += "(:init\n" + ToState(m_aStartState, false) + ")\n";
            sProblem += "(:goal (and\n" + ToState(m_aGoalState, true) + "))\n";
            sProblem += ")";
            return sProblem;
        }

        private string ToState(Stack<int>[] a, bool bGoalState)
        {
            string sState = "";// "(and\n";
            for(int iArm = 0 ; iArm < Arms ; iArm++)
                foreach (int i in m_lAgentStacks[iArm])
                    sState += "\t(in-stack T" + i + " S" + i + ")\n";
            for (int iStack = 0; iStack < a.Length; iStack++)
            {
                List<int> lStack = a[iStack].ToList();
                if (!bGoalState)
                {
                    //sState += "\t(in-stack T" + iStack + " S" + iStack + ")\n";
                    if (lStack.Count == 0)
                        sState += "\t(clear T" + iStack + " S" + iStack + ")\n";
                }
                for (int i = 0; i < a[iStack].Count; i++)
                {
                    int iBlock = lStack[i];
                    //sState += "\t(in-stack B" + iBlock + " S" + iStack + ")\n";
                    if (i == 0)
                    {
                        sState += "\t(on B" + iBlock + " T" + iStack + " S" + iStack + ")\n";
                    }
                    else
                    {
                        sState += "\t(on B" + iBlock + " B" + lStack[i - 1] + " S" + iStack + ")\n";
                    }
                    if (i == a[iStack].Count - 1)
                    {
                        sState += "\t(clear B" + iBlock + " S" + iStack + ")\n";
                    }
                    sState += "\t(in-stack B" + iBlock + " S" + iStack + ")\n";
                }

            }
            //sState += ")";
            return sState;
        }


        private string ToPartialState(Stack<int>[] a, int iArm, bool bGoalState)
        {
            string sState = "";// "(and\n";
            foreach (int i in m_lAgentStacks[iArm])
                sState += "\t(in-stack T" + i + " S" + i + ")\n";
            foreach (int iStack in m_lAgentStacks[iArm])
            {
                List<int> lStack = a[iStack].ToList();
                if (!bGoalState)
                {
                    //sState += "\t(in-stack T" + iStack + " S" + iStack + ")\n";
                    if (lStack.Count == 0)
                        sState += "\t(clear T" + iStack + " S" + iStack + ")\n";
                }
                for (int i = 0; i < a[iStack].Count; i++)
                {
                    int iBlock = lStack[i];
                    //sState += "\t(in-stack B" + iBlock + " S" + iStack + ")\n";
                    if (i == 0)
                    {
                        sState += "\t(on B" + iBlock + " T" + iStack + " S" + iStack + ")\n";
                    }
                    else
                    {
                        sState += "\t(on B" + iBlock + " B" + lStack[i - 1] + " S" + iStack + ")\n";
                    }
                    if (i == a[iStack].Count - 1)
                    {
                        sState += "\t(clear B" + iBlock + " S" + iStack + ")\n";
                    }
                    sState += "\t(in-stack B" + iBlock + " S" + iStack + ")\n";
                }

            }
            //sState += ")";
            return sState;
        }

        private string GenerateConstants(int iArm)
        {
            int iBlock = 0;
            string sObjects = "(:constants\n";
            for (iBlock = 0; iBlock < Blocks; iBlock++)
            {
                sObjects += "\t B" + iBlock + " - BLOCK\n";
            }
            for (int i = 0; i < Arms * MaxStacksPerAgent + 1; i++)
            {
                sObjects += "\t T" + i + " - BLOCK\n";
            }
            //sObjects += "\t T - BLOCK\n";

            sObjects += "\t A" + iArm + " - ARM\n";//arm is not private because we need the action putting a block in the public stack to be public
            
            foreach(int iStack in m_lAgentStacks[iArm])
            {
                if(m_lPublicStacks.Contains(iStack))
                    sObjects += "\t S" + iStack + " - STACK\n";
                else
                    sObjects += "\t (:private S" + iStack + " - STACK)\n";
            }
            sObjects += ")";
            return sObjects;
        }


        private string GenerateConstants()
        {
            int iBlock = 0, iArm = 0;
            string sObjects = "(:constants\n";
            for (iBlock = 0; iBlock < Blocks; iBlock++)
            {
                sObjects += "\t B" + iBlock + " - BLOCK\n";
            }
            for (int i = 0; i < Arms * MaxStacksPerAgent + 1; i++)
            {
                sObjects += "\t T" + i + " - BLOCK\n";
            }
            //sObjects += "\t T - BLOCK\n";
            for (iArm = 0; iArm < Arms; iArm++)
            {
                sObjects += "\t A" + iArm + " - ARM\n";
            }
            for (int i = 0; i < Arms * MaxStacksPerAgent + 1; i++)
            {
                sObjects += "\t S" + i + " - STACK\n";
            }
            sObjects += ")";
            return sObjects;
        }

        private string GeneratePredicates()
        {
            string sPredicates = "(:predicates\n";
            sPredicates += "\t(on ?b1 - BLOCK ?b2 - BLOCK ?s - STACK)\n";
            sPredicates += "\t(in-stack ?b - BLOCK ?s - STACK)\n";
            sPredicates += "\t(clear ?b - BLOCK ?s - STACK)\n";
            sPredicates += ")\n";
            return sPredicates;
        }

        private string GenerateActions()
        {
            string sActions = "";
            for (int iArm = 0; iArm < Arms; iArm++)
            {
                sActions += GenerateActions(iArm);
            }
            return sActions;
        }
        private string GenerateActions(int iArm)
        {
            string sActions = "";

                for (int i = 0; i < m_lAgentStacks[iArm].Count - 1; i++)
                {
                    int iStack1 = m_lAgentStacks[iArm][i];
                    int iStack2 = m_lAgentStacks[iArm][i + 1];
                    sActions += GenerateMove(iArm, iStack1, iStack2) + "\n";
                    sActions += GenerateMove(iArm, iStack2, iStack1) + "\n";
                }
            
            return sActions;
        }

        private string GenerateMove(int iArm, int iSourceStack, int iTargetStack)
        {
            string sAction = "(:action move-a" + iArm + "-s" + iSourceStack + "-s" + iTargetStack + "\n";
            sAction += ":parameters (?bMove - BLOCK ?bSource - BLOCK ?bTarget - BLOCK)\n";
            sAction += ":precondition (and (on ?bMove ?bSource S" + iSourceStack + ") (in-stack ?bSource S" + iSourceStack + ") (clear ?bMove S" + iSourceStack + ") (clear ?bTarget S" + iTargetStack + ") (in-stack ?bTarget S" + iTargetStack + ") )\n";
            sAction += ":effect (and (not (on ?bMove ?bSource S" + iSourceStack + ")) (not (in-stack ?bMove S" + iSourceStack + ")) (on ?bMove ?bTarget S" + iTargetStack + ") (in-stack ?bMove S" + iTargetStack + ") (clear ?bSource S" + iSourceStack + ") (not  (clear ?bMove S" + iSourceStack + ")) (clear ?bMove S" + iTargetStack + ") (not (clear ?bTarget S" + iTargetStack + ")))\n";
            sAction += ")\n";
            return sAction;
        }


        public void WriteDomain(string sPath)
        {
            DirectoryInfo di = new DirectoryInfo(sPath);
            if (!di.Exists)
                di.Create();
            StreamWriter sw = new StreamWriter(sPath + @"\d.pddl");
            sw.Write(GenerateDomain());
            sw.Close();
        }


        public void WriteFactoredDomains(string sPath)
        {
            DirectoryInfo di = new DirectoryInfo(sPath);
            if (!di.Exists)
                di.Create();
            for (int iArm = 0; iArm < Arms; iArm++)
            {
                StreamWriter sw = new StreamWriter(sPath + @"\domain-arm" + iArm + ".pddl");
                sw.Write(GenerateFactoredDomain(iArm));
                sw.Close();
            }
        }

        private string GenerateDomain()
        {
            string sDomain = "(define \n";
            sDomain += "(domain " + Name + ")\n";
            sDomain += "(:types BLOCK ARM STACK)\n";
            sDomain += GenerateConstants();
            sDomain += GeneratePredicates();
            sDomain += GenerateActions();
            sDomain += ")";
            return sDomain;
        }


        private string GenerateFactoredDomain(int iArm)
        {
            string sDomain = "(define \n";
            sDomain += "(domain " + Name + "-arm" + iArm + ")\n";
            sDomain += "(:types BLOCK ARM STACK)\n";
            sDomain += GenerateConstants(iArm);
            sDomain += GeneratePredicates();
            sDomain += GenerateActions(iArm);
            sDomain += ")";
            return sDomain;
        }


        public string Name { get { return "MABlocksWorld2-" + Arms + "-" + Blocks + "-" + MaxStacksPerAgent; } }
    }
}