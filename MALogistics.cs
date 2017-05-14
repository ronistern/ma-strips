using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;

namespace Planning
{
    class MALogistics
    {
        public int Packages { get; private set; }
        public int Areas { get; private set; }
        public int MaxCitiesPerArea { get; private set; }
        public int TotalCities { get; private set; }
        private Dictionary<int,int> m_aStartState, m_aGoalState;
        private List<List<int>> m_lCitiesForArea;
        private HashSet<int> m_lPublicCities;
        public MALogistics(int cPackages, int cAreas, int cMaxCitiesPerArea)
        {
            Packages = cPackages;
            Areas = cAreas;
            MaxCitiesPerArea = cMaxCitiesPerArea;

            m_lPublicCities = new HashSet<int>();
            m_lCitiesForArea = new List<List<int>>();
            int iCity = 0;
            for (int iArea = 0; iArea < Areas; iArea++)
            {
                m_lCitiesForArea.Add(new List<int>());
                int cCities = 0;
                //if (iArea % 3 == 0)
                cCities = RandomGenerator.Next(cMaxCitiesPerArea + 1) + 1;
               // else
                //    cCities = RandomGenerator.Next(cMaxCitiesPerArea / 2 + 1) + 1;
                for (int i = 0; i < cCities; i++)
                    m_lCitiesForArea[iArea].Add(iCity + i);
                iCity += cCities - 1;
            }
            TotalCities = iCity + 1;

            m_lCitiesForArea[Areas / 2].Add(0);

            m_aStartState = new Dictionary<int, int>();
            for (int iPackage = 0; iPackage < Packages; iPackage++)
            {
                m_aStartState[iPackage] = RandomGenerator.Next(TotalCities);
            }
            m_aGoalState = new Dictionary<int, int>();
            for (int iPackage = 0; iPackage < Packages; iPackage++)
            {
                m_aGoalState[iPackage] = RandomGenerator.Next(TotalCities);
            }

            for (iCity = 0; iCity < TotalCities; iCity++)
            {
                int cCityAreas = 0;
                for (int iArea = 0; iArea < Areas; iArea++)
                {
                    if (m_lCitiesForArea[iArea].Contains(iCity))
                        cCityAreas++;

                }
                if (cCityAreas > 1)
                    m_lPublicCities.Add(iCity);
            }
        }

        public void WriteProblem(string sPathName)
        {
            StreamWriter sw = new StreamWriter(sPathName + @"\p.pddl");
            sw.WriteLine(GenerateProblem());
            sw.Close();
        }

        public void WriteFactoredProblems(string sPathName)
        {
            for (int iArea = 0; iArea < Areas; iArea++)
            {
                StreamWriter sw = new StreamWriter(sPathName + @"\problem-a" + iArea + ".pddl");
                sw.WriteLine(GenerateProblem(iArea));
                sw.Close();
            }
        }


        private string GenerateProblem(int iArea)
        {
            string sProblem = "(define \n";
            sProblem += "(problem " + Name + "-a" + iArea + ")\n";
            sProblem += "(:domain " + Name + "-a" + iArea + ")\n";

            sProblem += "(:init\n";
            foreach (int iCity in m_lCitiesForArea[iArea])
                sProblem += "\t(city-in-area C" + iCity + " A" + iArea + ")\n";


            sProblem += "\t(truck-in-area T" + iArea + " A" + iArea + ")\n";
            sProblem += "\t(truck-in-city T" + iArea + " C" + m_lCitiesForArea[iArea].First() + ")\n";


            for (int iCity = 0; iCity < m_lCitiesForArea[iArea].Count - 1; iCity++)
            {
                sProblem += "\t(adj C" + m_lCitiesForArea[iArea][iCity + 1] + " C" + m_lCitiesForArea[iArea][iCity] + ")\n";
                sProblem += "\t(adj C" + m_lCitiesForArea[iArea][iCity] + " C" + m_lCitiesForArea[iArea][iCity + 1] + ")\n";
            }


            foreach (KeyValuePair<int, int> p in m_aStartState)
            {
                if (m_lCitiesForArea[iArea].Contains(p.Value))
                    sProblem += "\t(package-in-city P" + p.Key + " C" + p.Value + ")\n";
            }
            sProblem += ")\n";
            sProblem += "(:goal (and\n";
            foreach (KeyValuePair<int, int> p in m_aGoalState)
                if (m_lCitiesForArea[iArea].Contains(p.Value))
                    sProblem += "\t(package-in-city P" + p.Key + " C" + p.Value + ")\n";
            sProblem += "))\n";
            sProblem += ")";
            return sProblem;
        }


        private string GenerateProblem()
        {
            string sProblem = "(define \n";
            sProblem += "(problem MALogistics-" + Areas + "-" + MaxCitiesPerArea + "-" + Packages + ")\n";
            sProblem += "(:domain MALogistics-" + Areas + "-" + MaxCitiesPerArea + "-" + Packages + ")\n";

            sProblem += "(:init\n";
            for (int iArea = 0; iArea < Areas; iArea++)
            {
                foreach (int iCity in m_lCitiesForArea[iArea])
                    sProblem += "\t(city-in-area C" + iCity + " A" + iArea + ")\n";
            }
            for (int iArea = 0; iArea < Areas; iArea++)
            {
                sProblem += "\t(truck-in-area tru" + iArea + " A" + iArea + ")\n";
                sProblem += "\t(truck-in-city tru" + iArea + " C" + m_lCitiesForArea[iArea].First() + ")\n";
            }

            for (int iArea = 0; iArea < Areas; iArea++)
            {
                for (int iCity = 0; iCity < m_lCitiesForArea[iArea].Count - 1; iCity++)
                {
                    sProblem += "\t(adj C" + m_lCitiesForArea[iArea][iCity + 1] + " C" + m_lCitiesForArea[iArea][iCity] + ")\n";
                    sProblem += "\t(adj C" + m_lCitiesForArea[iArea][iCity] + " C" + m_lCitiesForArea[iArea][iCity + 1] + ")\n";
                }
            }



            foreach (KeyValuePair<int, int> p in m_aStartState)
                sProblem += "\t(package-in-city P" + p.Key + " C" + p.Value + ")\n";
            sProblem +=")\n";
            sProblem += "(:goal (and\n";
            foreach (KeyValuePair<int, int> p in m_aGoalState)
                sProblem += "\t(package-in-city P" + p.Key + " C" + p.Value + ")\n";
            sProblem += "))\n";
            sProblem += ")";
            return sProblem;
        }

        private string GenerateConstants()
        {
            int iPackage = 0, iArea = 0;
            string sObjects = "(:constants\n";
            for (iPackage = 0; iPackage < Packages; iPackage++)
            {
                sObjects += "\t P" + iPackage + " - PACKAGE\n";
            }
            for (int i = 0; i < TotalCities; i++)
            {
                sObjects += "\t C" + i + " - CITY\n";
            }
            for (iArea = 0; iArea < Areas; iArea++)
            {
                sObjects += "\t A" + iArea + " - AREA\n";
            }
            for (iArea = 0; iArea < Areas; iArea++)
            {
                sObjects += "\t T" + iArea + " - TRUCK\n";
            }
            sObjects += ")";
            return sObjects;
        }

        private string GenerateConstants(int iArea)
        {
            int iPackage = 0;
            string sObjects = "(:constants\n";
            for (iPackage = 0; iPackage < Packages; iPackage++)
            {
                sObjects += "\t P" + iPackage + " - PACKAGE\n";
            }
            foreach(int iCity in m_lCitiesForArea[iArea])
            {
                if(m_lPublicCities.Contains(iCity))
                    sObjects += "\t C" + iCity + " - CITY\n";
                else
                    sObjects += "\t (:private C" + iCity + " - CITY)\n";
            }
            sObjects += "\t A" + iArea + " - AREA\n";
            
            sObjects += "\t (:private T" + iArea + " - TRUCK)\n";
            
            sObjects += ")";
            return sObjects;
        }

        private string GeneratePredicates()
        {
            string sPredicates = "(:predicates\n";
            sPredicates += "\t(adj ?c1 - CITY ?c2 - CITY)\n";
            sPredicates += "\t(package-in-city ?p - PACKAGE ?c - CITY)\n";
            sPredicates += "\t(city-in-area ?c - CITY ?a - AREA)\n";
            sPredicates += "\t(truck-in-city ?T - TRUCK ?c - CITY)\n";
            sPredicates += "\t(truck-in-area ?T - TRUCK ?a - AREA)\n";
            sPredicates += "\t(package-on-truck ?p - PACKAGE ?T - TRUCK)\n";
            sPredicates += ")\n";
            return sPredicates;
        }


        private string GenerateActions()
        {
            string sActions = "";
            sActions += GenerateDrive();
            sActions += GenerateLoad();
            sActions += GenerateUnload();
            return sActions;
        }

        private string GenerateDrive()
        {
            string sAction = "(:action drive\n";
            sAction += ":parameters (?T - TRUCK ?cSource - CITY ?cTarget - CITY ?a - AREA)\n";
            sAction += ":precondition (and (adj ?cSource ?cTarget) (truck-in-city ?T ?cSource) (city-in-area ?cSource ?a) (city-in-area ?cTarget ?a) (truck-in-area ?T ?a))\n";
            sAction += ":effect (and (not (truck-in-city ?T ?cSource)) (truck-in-city ?T ?cTarget))\n";
            sAction += ")\n";
            return sAction;
        }

        private string GenerateLoad()
        {
            string sAction = "(:action load\n";
            sAction += ":parameters (?p - PACKAGE ?T - TRUCK ?c - CITY)\n";
            sAction += ":precondition (and (truck-in-city ?T ?c) (package-in-city ?p ?c))\n";
            sAction += ":effect (and (not (package-in-city ?p ?c)) (package-on-truck ?p ?T))\n";
            sAction += ")\n";
            return sAction;

        }
        private string GenerateUnload()
        {
            string sAction = "(:action unload\n";
            sAction += ":parameters (?p - PACKAGE ?T - TRUCK ?c - CITY)\n";
            sAction += ":precondition (and (truck-in-city ?T ?c) (package-on-truck ?p ?T))\n";
            sAction += ":effect (and (not (package-on-truck ?p ?T)) (package-in-city ?p ?c))\n";
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
            for (int iArea = 0; iArea < Areas; iArea++)
            {
                StreamWriter sw = new StreamWriter(sPath + @"\domain-a" + iArea + ".pddl");
                sw.Write(GenerateDomain(iArea));
                sw.Close();
            }
        }
        private string GenerateDomain(int iArea)
        {
            string sDomain = "(define \n";
            sDomain += "(domain " + Name + "-a" + iArea + ")\n";
            sDomain += "(:types TRUCK PACKAGE CITY AREA)\n";
            sDomain += GenerateConstants(iArea);
            sDomain += GeneratePredicates();
            sDomain += GenerateActions();
            sDomain += ")";
            return sDomain;
        }

        private string GenerateDomain()
        {
            string sDomain = "(define \n";
            sDomain += "(domain MALogistics-" + Areas + "-" + MaxCitiesPerArea + "-" + Packages + ")\n";
            sDomain += "(:types TRUCK PACKAGE CITY AREA)\n";
            sDomain += GenerateConstants();
            sDomain += GeneratePredicates();
            sDomain += GenerateActions();
            sDomain += ")";
            return sDomain;
        }


        public string Name { get { return "MALogistics-" + Areas + "-" + MaxCitiesPerArea + "-" + Packages; } }
    }
}