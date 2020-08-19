package com.github.peterzeller.logiceval.utils

import com.github.peterzeller.logiceval.SimpleLogic

import scala.collection.MapView

case class HMap[K[_], V[_]](map: Map[K[_], V[_]] = Map[K[_], V[_]]()) {
  def contains(key: K[_]): Boolean =
    map.contains(key)

  def values: Iterable[V[_]] = map.values

  def getOrElse[T](k: K[T], default: => V[T]): V[T] =
    map.getOrElse(k, default).asInstanceOf[V[T]]


  def apply[T](key: K[T]): V[T] =
    map(key).asInstanceOf[V[T]]

  def get[T](key: K[T]): Option[V[T]] =
    map.get(key).asInstanceOf[Option[V[T]]]

  def +[T](p: (K[T], V[T])): HMap[K, V] =
    copy[K,V](map + p.asInstanceOf[(K[_], V[_])])

  def view: MapView[K[_], V[_]] = map.view

  def filter(pred: ((K[_], V[_])) => Boolean): MapView[K[_], V[_]] = view.filter(pred)

}
