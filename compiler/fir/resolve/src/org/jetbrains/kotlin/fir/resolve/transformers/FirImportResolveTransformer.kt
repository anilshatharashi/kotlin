/*
 * Copyright 2010-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license
 * that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.fir.resolve.transformers

import org.jetbrains.kotlin.fir.FirElement
import org.jetbrains.kotlin.fir.FirSession
import org.jetbrains.kotlin.fir.declarations.FirFile
import org.jetbrains.kotlin.fir.declarations.FirImport
import org.jetbrains.kotlin.fir.declarations.impl.FirResolvedImportImpl
import org.jetbrains.kotlin.fir.resolve.FirSymbolProvider
import org.jetbrains.kotlin.fir.visitors.CompositeTransformResult
import org.jetbrains.kotlin.fir.visitors.compose
import org.jetbrains.kotlin.name.ClassId
import org.jetbrains.kotlin.name.FqName

class FirImportResolveTransformer() : FirAbstractTreeTransformer() {
    override fun <E : FirElement> transformElement(element: E, data: Nothing?): CompositeTransformResult<E> {
        return element.compose()
    }

    private lateinit var symbolProvider: FirSymbolProvider

    private lateinit var session: FirSession

    constructor(session: FirSession) : this() {
        this.session = session
        // TODO: clarify this
        symbolProvider = FirSymbolProvider.getInstance(session)
    }

    override fun transformFile(file: FirFile, data: Nothing?): CompositeTransformResult<FirFile> {
        session = file.fileSession
        symbolProvider = FirSymbolProvider.getInstance(file.fileSession)
        return file.also { it.transformChildren(this, null) }.compose()
    }

    override fun transformImport(import: FirImport, data: Nothing?): CompositeTransformResult<FirImport> {
        val fqName = import.importedFqName?.takeUnless { it.isRoot } ?: return import.compose()

        if (import.isAllUnder) {
            return transformImportForFqName(fqName, import)
        }

        val parentFqName = fqName.parent()
        return transformImportForFqName(parentFqName, import)
    }

    private fun transformImportForFqName(fqName: FqName, delegate: FirImport): CompositeTransformResult<FirImport> {
        val (packageFqName, relativeClassFqName) = resolveToPackageOrClass(fqName) ?: return delegate.compose()
        return FirResolvedImportImpl(session, delegate, packageFqName, relativeClassFqName).compose()
    }

    private fun resolveToPackageOrClass(fqName: FqName): PackageOrClass? {
        var currentPackage = fqName

        val pathSegments = fqName.pathSegments()
        var prefixSize = pathSegments.size
        while (!currentPackage.isRoot) {
            if (symbolProvider.getPackage(currentPackage) != null) {
                break
            }
            currentPackage = currentPackage.parent()
            prefixSize--
        }

        if (currentPackage == fqName) return PackageOrClass(currentPackage, null)
        val relativeClassFqName =
            FqName.fromSegments((prefixSize until pathSegments.size).map { pathSegments[it].asString() })

        val classId = ClassId(currentPackage, relativeClassFqName, false)
        if (symbolProvider.getClassLikeSymbolByFqName(classId) == null) return null

        return PackageOrClass(currentPackage, relativeClassFqName)
    }

    private data class PackageOrClass(val packageFqName: FqName, val relativeClassFqName: FqName?)
}
