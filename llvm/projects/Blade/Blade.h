#ifndef BLADE_H
#define BLADE_H

#include "llvm/ADT/SmallSet.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

class OldBladeNode;

class BladeEdge {
 public:
  unsigned int weight;
  OldBladeNode* target;

 BladeEdge(unsigned int weight, OldBladeNode* target)
   : weight(weight), target(target) {}

  bool operator==(const BladeEdge other) const;

  bool operator<(const BladeEdge& other) const;
};

class OldBladeNode {
public:
  /// Discriminator for LLVM-style RTTI (dyn_cast<> et al.)
  enum BladeNodeKind {
    BNK_DistinguishedNode,
    BNK_ValueDefNode,
    BNK_InstSinkNode
  };

private:
  const BladeNodeKind kind;
  SmallSet<BladeEdge, 16> edges;

protected:
  virtual bool isEqual(const OldBladeNode& other) const = 0;
  virtual bool isLessThan(const OldBladeNode &other) const = 0;

public:
  BladeNodeKind getKind() const { return kind; }
  OldBladeNode(BladeNodeKind kind) : kind(kind) {}

  static bool classof(const OldBladeNode* node);

  bool operator==(const OldBladeNode& other) const;
  bool operator<(const OldBladeNode& other) const;

  void addEdge(BladeEdge edge);
  void removeEdge(BladeEdge edge);
  bool hasEdgeTo(const OldBladeNode &other) const;

  virtual raw_ostream& outputNode(raw_ostream& os) const = 0;
  void outputEdges(raw_ostream& os) const;
  friend raw_ostream& operator<<(raw_ostream& os, OldBladeNode const &node) {
    return node.outputNode(os);
  }
};

#endif BLADE_H
