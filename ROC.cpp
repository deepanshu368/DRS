#include <bits/stdc++.h>
#include <boost/dynamic_bitset.hpp>
#include <fstream>
using namespace std;

typedef struct
{
    boost::dynamic_bitset<unsigned long> lhs;
    boost::dynamic_bitset<unsigned long> rhs;
} implicationBS;

typedef struct
{
    implicationBS imp;
    long long int discriminativity;
} implicationWithDisc;

int numAttrs;
vector<boost::dynamic_bitset<unsigned long>> objInpBS;
vector<boost::dynamic_bitset<unsigned long>> attrInpBS;
vector<int> objectLabels, assignedObjectLabels, positiveObjects, negativeObjects;
vector<implicationBS> implications;
long long discriminativityFactor;
vector<int> totalAssociationRules(50, 0), followedAssociationRules(30, 0);
vector<pair<int, int>> trueAndOurLabels;

boost::dynamic_bitset<unsigned long> attrVectorToAttrBS(vector<int> &attrVec)
{
    boost::dynamic_bitset<unsigned long> ans(numAttrs);

    for (int i = 0; i < attrVec.size(); i++)
    {
        ans[attrVec[i]] = true;
    }
    // //cout<<"BS = "<< ans <<"\n";
    return ans;
}

void readContext(ifstream &contextFile)
{
    string line;

    while (getline(contextFile, line))
    {
        stringstream ss(line);
        vector<int> object;
        string word;

        while (ss >> word)
        {
            object.push_back(stoi(word));
        }

        objInpBS.push_back(attrVectorToAttrBS(object));
    }

    contextFile.close();

    attrInpBS = vector<boost::dynamic_bitset<unsigned long>>(numAttrs, boost::dynamic_bitset<unsigned long> (objInpBS.size() + 1).reset());
    for(int i = 0; i < objInpBS.size(); i++)
    {
        for(int j = 0; j < objInpBS[i].size(); j++){
            if(objInpBS[i][j])
            {
                attrInpBS[j][i] = true;
            }
        }
    }
}

void readLabels(ifstream &labelInput)
{
    int temp;
    int oID = 0;

    while (labelInput >> temp)
    {
        objectLabels.push_back(1-temp);

        if (temp == 0)
            negativeObjects.push_back(oID);
        else
            positiveObjects.push_back(oID);

        oID++;
    }

    labelInput.close();
}

void getImplicationsBS(ifstream &approxFile)
{
    string line;
    getline(approxFile, line);

    while (getline(approxFile, line))
    {
        stringstream ss(line);
        string word;
        pair<vector<int>, vector<int>> implication;
        implicationBS bSImplication;
        while (ss >> word)
        {
            if (word[0] == '=')
                break;

            implication.first.push_back(stoi(word));
        }

        while (ss >> word)
        {
            implication.second.push_back(stoi(word));
        }

        bSImplication.lhs = attrVectorToAttrBS(implication.first);
        bSImplication.rhs = attrVectorToAttrBS(implication.second);
        implications.push_back(bSImplication);
    }

    approxFile.close();
}

// Given L and X, find L(X).
boost::dynamic_bitset<unsigned long> closureBS(vector<implicationBS> &basis, boost::dynamic_bitset<unsigned long> X)
{
    if (basis.size() == 0)
        return X;
    vector<bool> cons;
    for (int i = 0; i <= basis.size(); i++)
        cons.push_back(false);
    bool changed = true;

    while (changed)
    {
        changed = false;

        for (int i = 0; i < basis.size(); i++)
        {
            if (cons[i] == true)
                continue;

            if (basis[i].lhs.is_subset_of(X))
            {
                cons[i] = true;

                if (!basis[i].rhs.is_subset_of(X))
                {
                    X |= basis[i].rhs;
                    changed = true;
                    break;
                }
            }
        }
    }

    return X;
}

vector<int> rulesLabels;
vector<implicationWithDisc> rulesWithDisc;
int kValue;
bool compareInterval(implicationWithDisc I1, implicationWithDisc I2)
{
    return I1.discriminativity > I2.discriminativity;
}
vector<int> attrBSToAttrVector(boost::dynamic_bitset<unsigned long> &attrBS)
{
    vector<int> ans;
    // //cout <<"BS = "<< attrBS <<"\n";

    for (int i = 0; i < attrBS.size(); i++)
    {
        if (attrBS[i])
            ans.push_back(i);
    }

    return ans;
}

void printVector(vector<int> &A)
{
    for (auto x : A)
    {
        cout << x << " ";
    }
}


boost::dynamic_bitset<unsigned long> calculateTau(implicationBS &rule)
{
    boost::dynamic_bitset<unsigned long> tau(attrInpBS[0].size());
    boost::dynamic_bitset<unsigned long> body(attrInpBS[0].size());

    tau.reset();
    body.reset();
    body = rule.lhs | rule.rhs;

    int i = 0;
    for(i; i < body.size(); i++)
    {
        if(body[i] == true)
        {
            // has i-th attr
            tau = attrInpBS[i];
            break;
        }
    }

    for(i = i + 1; i < body.size(); i++)
    {
        if(body[i] == true)
        {
            tau = tau & attrInpBS[i];
        }
    }

    return tau;
}

vector<int> ruleTauSize;
void calculateTauSizeOfEachRule()
{
    ruleTauSize.clear();
    for(int i = 0; i < rulesWithDisc.size(); i++)
    {
        ruleTauSize.push_back(calculateTau(rulesWithDisc[i].imp).count());
    }
}

void assignLabelsToObjects()
{
    calculateTauSizeOfEachRule();

    for(int i = 0; i < objInpBS.size(); i++){
        int label = 0, max_coverage = -1, classZeroCount = 0, classOneCount = 0;
        for(int j = 0; j < rulesWithDisc.size(); j++)
        {
            boost::dynamic_bitset<unsigned long> body = rulesWithDisc[j].imp.lhs | rulesWithDisc[j].imp.rhs;
            if(body.is_subset_of(objInpBS[i]))
            {
                if(rulesLabels[j] == 0)
                {
                    classZeroCount++;
                }
                if(rulesLabels[j] == 1)
                {
                    classOneCount++;
                }
                if(ruleTauSize[j] > max_coverage)
                {
                    label = rulesLabels[j];
                    max_coverage = ruleTauSize[j];
                }
            }
        }
        // cout << classZeroCount << " " << classOneCount << " " << label << "\n";
        if(classZeroCount > classOneCount)
        {
            assignedObjectLabels.push_back(0);
        }
        else if(classZeroCount < classOneCount)
        {
            assignedObjectLabels.push_back(1);
        }
        else
        {
            assignedObjectLabels.push_back(label);
        }
    }

}



bool compare(pair<int, int> p1, pair<int, int> p2){
    if(p1.first==p2.first){
        if(p1.first==0){
            return p1.second > p2.second;
        }
        else{
            return p1.second < p2.second;
        }
    }
    return p1.first < p2.first;
}

int sumOfRankings=0, countObjectOurLabel0=0, countObjectOurLabel1=0;
void calculateMetrics(){
    int sum=0;
    int count0=0, count1=0;
    for(int i=0;i<trueAndOurLabels.size();i++){
        if(trueAndOurLabels[i].second==1){
            sum+= i+1;
            count1++;
        }
        else{
            count0++;
        }
    }
    sumOfRankings=sum, countObjectOurLabel0=count0, countObjectOurLabel1=count1;
}
float mww(){
    return (2*(float)sumOfRankings - (countObjectOurLabel1*(countObjectOurLabel1+1)))/(2*countObjectOurLabel0*countObjectOurLabel1);
}

int main(int argc, char **argv)
{
    numAttrs = stoi(argv[1]);
    ifstream implicationsFile(argv[2]), contextFile(argv[3]), labelsFile(argv[4]);
    kValue = stoi(argv[5]);
    getImplicationsBS(implicationsFile);
    readContext(contextFile);
    readLabels(labelsFile);
    long long int classZeroCoveredByR = 0, classZeroNotCoveredByR = 0, classOneCoveredByR = 0, classOneNotCoveredByR = 0;
    for (int i = 0; i < implications.size(); i++)
    {
        boost::dynamic_bitset<unsigned long> unionOfRule = implications[i].lhs | implications[i].rhs;
        for (int j = 0; j < objInpBS.size(); j++)
        {
            if (unionOfRule.is_subset_of(objInpBS[j]))
            {
                if (objectLabels[j] == 0)
                {
                    classZeroCoveredByR++;
                }
                else
                {
                    classOneCoveredByR++;
                }
            }
            else
            {
                if (objectLabels[j] == 0)
                {
                    classZeroNotCoveredByR++;
                }
                else
                {
                    classOneNotCoveredByR++;
                }
            }
        }
        if (classZeroCoveredByR * classOneNotCoveredByR > classOneCoveredByR * classZeroNotCoveredByR)
        {
            rulesLabels.push_back(0);
            rulesWithDisc.push_back({implications[i], classZeroCoveredByR * classOneNotCoveredByR});
        }
        else
        {   if(classZeroCoveredByR * classOneNotCoveredByR==classOneCoveredByR * classZeroNotCoveredByR){
            cout<<"EQUAL"<<endl;
        }
            rulesLabels.push_back(1);
            rulesWithDisc.push_back({implications[i], classOneCoveredByR * classZeroNotCoveredByR});
        }
    }
    std::sort(rulesWithDisc.begin(), rulesWithDisc.end(), compareInterval);
    int iterCount;
    if (kValue < rulesWithDisc.size())
    {
        iterCount = kValue;
    }
    else
    {
        iterCount = rulesWithDisc.size();
    }

    // store only the topk rules
    rulesWithDisc.resize(kValue);
    for (int i = 0; i < iterCount; i++)
    {
        // cout<<"Iter "<<i<<endl;
        vector<int> vecLHS = attrBSToAttrVector(rulesWithDisc[i].imp.lhs);
        vector<int> vecRHS = attrBSToAttrVector(rulesWithDisc[i].imp.rhs);
        printVector(vecLHS);
        cout << " => ";
        printVector(vecRHS);
        cout << " #" << rulesWithDisc[i].discriminativity << " "
             << "label " << rulesLabels[i];
        cout << endl;
    }

    implications.clear();
    assignLabelsToObjects();

    //calculate ROC

    for(int i=0;i<objectLabels.size();i++){
        trueAndOurLabels.push_back({objectLabels[i], assignedObjectLabels[i]});
    }

    std::sort(trueAndOurLabels.begin(), trueAndOurLabels.end(), compare);
    calculateMetrics();
    float mww10=mww();
    cout<<"count0"<<countObjectOurLabel0<<" count1"<<countObjectOurLabel1<<endl;
    //invert all the labels
    for(int i=0;i<trueAndOurLabels.size();i++){
        trueAndOurLabels[i]= {1-trueAndOurLabels[i].first, 1-trueAndOurLabels[i].second};
    }
    std::sort(trueAndOurLabels.begin(), trueAndOurLabels.end(), compare);

    calculateMetrics();
    float mww01=mww();

    float roc= (mww10 + mww01)/2;

    cout<<"ROC "<<roc<<endl;
    return 0;
}